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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
size_t lean_array_size(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "uf"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 205, 59, 238, 58, 10, 87, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1024257597) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 129, 108, 56, 55, 49, 14, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 154, 94, 170, 251, 184, 218, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 67, 3, 239, 77, 159, 140, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(117, 32, 14, 232, 66, 168, 32, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0;
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
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structures"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeout"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "trimProofs"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 194, 200, 171, 14, 58, 44, 165)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(185, 35, 170, 33, 56, 163, 92, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(138, 62, 200, 17, 191, 250, 20, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(172, 213, 62, 248, 144, 193, 119, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "shortCircuit"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "solverMode"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(114, 180, 226, 180, 157, 207, 20, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 98, 5, 93, 176, 49, 199, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(57, 132, 100, 173, 170, 111, 204, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(33, 94, 75, 99, 14, 104, 154, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "embeddedConstraintSubst"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "enums"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fixedInt"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(70, 215, 84, 227, 237, 239, 174, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(100, 69, 255, 25, 239, 243, 175, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(31, 99, 203, 82, 4, 19, 166, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "acNf"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "andFlattening"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "binaryProofs"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cegarRounds"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(92, 54, 212, 79, 173, 215, 145, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(92, 177, 215, 204, 53, 6, 208, 155)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24_value),LEAN_SCALAR_PTR_LITERAL(50, 143, 191, 247, 230, 85, 201, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 227, 134, 102, 248, 164, 241, 21)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(209, 218, 38, 182, 3, 205, 122, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30_value;
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 102, .m_capacity = 102, .m_length = 101, .m_data = "` cannot be used in a `types` clause, only non-recursive structures and enum inductives are supported"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTypes"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 159, 97, 61, 240, 205, 127, 31)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unexpected `types` clause"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "simp theorems used by bv_normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "bvNormalizeExt"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__6_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 148, 199, 156, 241, 6, 144, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_));
v___x_133_ = 0;
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_));
v___x_135_ = l_Lean_registerTraceClass(v___x_132_, v___x_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2____boxed(lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_();
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object* v_name_138_, lean_object* v_decl_139_, lean_object* v_ref_140_){
_start:
{
lean_object* v_defValue_142_; lean_object* v_descr_143_; lean_object* v_deprecation_x3f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_defValue_142_ = lean_ctor_get(v_decl_139_, 0);
v_descr_143_ = lean_ctor_get(v_decl_139_, 1);
v_deprecation_x3f_144_ = lean_ctor_get(v_decl_139_, 2);
lean_inc(v_defValue_142_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v_defValue_142_);
lean_inc(v_deprecation_x3f_144_);
lean_inc_ref(v_descr_143_);
lean_inc_n(v_name_138_, 2);
v___x_146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_146_, 0, v_name_138_);
lean_ctor_set(v___x_146_, 1, v_ref_140_);
lean_ctor_set(v___x_146_, 2, v___x_145_);
lean_ctor_set(v___x_146_, 3, v_descr_143_);
lean_ctor_set(v___x_146_, 4, v_deprecation_x3f_144_);
v___x_147_ = lean_register_option(v_name_138_, v___x_146_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v___x_147_, 0);
lean_dec(v_unused_156_);
v___x_149_ = v___x_147_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_dec(v___x_147_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
lean_inc(v_defValue_142_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_name_138_);
lean_ctor_set(v___x_151_, 1, v_defValue_142_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec(v_name_138_);
v_a_157_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_147_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_147_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_165_, lean_object* v_decl_166_, lean_object* v_ref_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(v_name_165_, v_decl_166_, v_ref_167_);
lean_dec_ref(v_decl_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_191_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(v___x_188_, v___x_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_();
return v_res_193_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
v___x_195_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___boxed(lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(lean_object* v_00_u03b1_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___boxed(lean_object* v_00_u03b1_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(v_00_u03b1_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(lean_object* v___x_223_, lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v___x_227_, lean_object* v_ctor_228_, lean_object* v_args_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_238_ = lean_string_dec_eq(v_ctor_228_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_240_ = lean_string_dec_eq(v_ctor_228_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_242_ = lean_string_dec_eq(v_ctor_228_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec_ref(v___x_227_);
lean_dec_ref(v___x_226_);
lean_dec_ref(v___x_225_);
lean_dec_ref(v___x_224_);
lean_dec_ref(v___x_223_);
v___x_243_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = l_Lean_Name_mkStr6(v___x_223_, v___x_224_, v___x_225_, v___x_226_, v___x_227_, v___x_241_);
v___x_245_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_244_);
v___x_246_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_244_, v___x_245_, v_args_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_258_; 
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v___x_246_, 0);
lean_dec(v_unused_259_);
v___x_248_ = v___x_246_;
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
else
{
lean_dec(v___x_246_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_250_ = 0;
v___x_251_ = lean_box(0);
v___x_252_ = l_Lean_Expr_const___override(v___x_244_, v___x_251_);
v___x_253_ = lean_box(v___x_250_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_254_);
v___x_256_ = v___x_248_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v___x_244_);
v_a_260_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_246_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_246_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
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
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = l_Lean_Name_mkStr6(v___x_223_, v___x_224_, v___x_225_, v___x_226_, v___x_227_, v___x_239_);
v___x_269_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_268_);
v___x_270_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_268_, v___x_269_, v_args_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_282_; 
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_283_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_274_ = 2;
v___x_275_ = lean_box(0);
v___x_276_ = l_Lean_Expr_const___override(v___x_268_, v___x_275_);
v___x_277_ = lean_box(v___x_274_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_278_);
v___x_280_ = v___x_272_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v___x_268_);
v_a_284_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_270_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_270_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = l_Lean_Name_mkStr6(v___x_223_, v___x_224_, v___x_225_, v___x_226_, v___x_227_, v___x_237_);
v___x_293_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_292_);
v___x_294_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_292_, v___x_293_, v_args_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_306_; 
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v___x_294_, 0);
lean_dec(v_unused_307_);
v___x_296_ = v___x_294_;
v_isShared_297_ = v_isSharedCheck_306_;
goto v_resetjp_295_;
}
else
{
lean_dec(v___x_294_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_306_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_298_ = 1;
v___x_299_ = lean_box(0);
v___x_300_ = l_Lean_Expr_const___override(v___x_292_, v___x_299_);
v___x_301_ = lean_box(v___x_298_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_302_);
v___x_304_ = v___x_296_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v___x_292_);
v_a_308_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_294_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_294_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___boxed(lean_object* v___x_316_, lean_object* v___x_317_, lean_object* v___x_318_, lean_object* v___x_319_, lean_object* v___x_320_, lean_object* v_ctor_321_, lean_object* v_args_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(v___x_316_, v___x_317_, v___x_318_, v___x_319_, v___x_320_, v_ctor_321_, v_args_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec_ref(v_args_322_);
lean_dec_ref(v_ctor_321_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___f_353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__2));
v___x_354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_355_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_354_, v___f_353_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___boxed(lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_box(0);
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_368_ = l_Lean_Expr_const___override(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__0));
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_box(0);
v___x_374_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___boxed(lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(lean_object* v_00_u03b1_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(v_00_u03b1_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(lean_object* v_msgData_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_env_402_; lean_object* v___x_403_; lean_object* v_toCold_404_; lean_object* v_mctx_405_; lean_object* v_lctx_406_; lean_object* v_options_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_401_ = lean_st_ref_get(v___y_399_);
v_env_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_401_);
v___x_403_ = lean_st_ref_get(v___y_397_);
v_toCold_404_ = lean_ctor_get(v___y_398_, 0);
v_mctx_405_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_mctx_405_);
lean_dec(v___x_403_);
v_lctx_406_ = lean_ctor_get(v___y_396_, 2);
v_options_407_ = lean_ctor_get(v_toCold_404_, 2);
lean_inc_ref(v_options_407_);
lean_inc_ref(v_lctx_406_);
v___x_408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_408_, 0, v_env_402_);
lean_ctor_set(v___x_408_, 1, v_mctx_405_);
lean_ctor_set(v___x_408_, 2, v_lctx_406_);
lean_ctor_set(v___x_408_, 3, v_options_407_);
v___x_409_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_msgData_395_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msgData_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_ref_424_; lean_object* v___x_425_; lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_ref_424_ = lean_ctor_get(v___y_421_, 2);
v___x_425_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_inc(v_ref_424_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v_ref_424_);
lean_ctor_set(v___x_430_, 1, v_a_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 1);
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(lean_object* v_ctor_445_, lean_object* v_args_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_465_ = lean_string_dec_eq(v_ctor_445_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_467_ = lean_string_dec_eq(v_ctor_445_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_469_ = lean_string_dec_eq(v_ctor_445_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_array_get_size(v_args_446_);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_475_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_474_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
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
goto v___jp_452_;
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = lean_array_get_size(v_args_446_);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_nat_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_488_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_487_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
goto v___jp_456_;
}
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_array_get_size(v_args_446_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_nat_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v___x_500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_501_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_500_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
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
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
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
goto v___jp_460_;
}
}
v___jp_452_:
{
uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = 0;
v___x_454_ = lean_box(v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
v___jp_456_:
{
uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = 2;
v___x_458_ = lean_box(v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
v___jp_460_:
{
uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = 1;
v___x_462_ = lean_box(v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object* v_ctor_510_, lean_object* v_args_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(v_ctor_510_, v_args_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_args_511_);
lean_dec_ref(v_ctor_510_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___f_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___f_525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0));
v___x_526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_527_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_526_, v___f_525_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___boxed(lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(lean_object* v_00_u03b1_535_, lean_object* v_msg_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_543_, lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(v_00_u03b1_543_, v_msg_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0));
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode(void){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object* v___x_559_, lean_object* v_ctor_560_, lean_object* v_args_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0));
v___x_769_ = lean_string_dec_eq(v_ctor_560_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_770_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_array_get_size(v_args_561_);
v___x_772_ = lean_unsigned_to_nat(15u);
v___x_773_ = lean_nat_dec_eq(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_775_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_774_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
goto v___jp_567_;
}
}
v___jp_567_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_568_);
lean_inc(v___x_569_);
v___x_570_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_569_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_572_);
lean_inc(v___x_573_);
v___x_574_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_573_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_unsigned_to_nat(2u);
v___x_577_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_576_);
lean_inc(v___x_577_);
v___x_578_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_577_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_580_);
lean_inc(v___x_581_);
v___x_582_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_581_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
v___x_584_ = lean_unsigned_to_nat(4u);
v___x_585_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_584_);
lean_inc(v___x_585_);
v___x_586_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_585_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = lean_unsigned_to_nat(5u);
v___x_589_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_588_);
lean_inc(v___x_589_);
v___x_590_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_589_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = lean_unsigned_to_nat(6u);
v___x_593_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_592_);
lean_inc(v___x_593_);
v___x_594_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_593_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = lean_unsigned_to_nat(7u);
v___x_597_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_596_);
lean_inc(v___x_597_);
v___x_598_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_597_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = lean_unsigned_to_nat(8u);
v___x_601_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_600_);
lean_inc(v___x_601_);
v___x_602_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_601_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = lean_unsigned_to_nat(9u);
v___x_605_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_604_);
lean_inc(v___x_605_);
v___x_606_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_605_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = lean_unsigned_to_nat(10u);
v___x_609_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_608_);
lean_inc(v___x_609_);
v___x_610_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_609_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = lean_unsigned_to_nat(11u);
v___x_613_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_612_);
lean_inc(v___x_613_);
v___x_614_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_613_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = lean_unsigned_to_nat(12u);
v___x_617_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_616_);
lean_inc(v___x_617_);
v___x_618_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v___x_617_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = lean_unsigned_to_nat(13u);
v___x_621_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_620_);
lean_inc(v___x_621_);
v___x_622_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_621_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_unsigned_to_nat(14u);
v___x_625_ = lean_array_get_borrowed(v___x_559_, v_args_561_, v___x_624_);
lean_inc(v___x_625_);
v___x_626_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_625_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_647_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_647_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_647_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_647_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___x_632_; uint8_t v___x_633_; uint8_t v___x_634_; uint8_t v___x_635_; uint8_t v___x_636_; uint8_t v___x_637_; uint8_t v___x_638_; uint8_t v___x_639_; uint8_t v___x_640_; uint8_t v___x_641_; uint8_t v___x_642_; uint8_t v___x_643_; lean_object* v___x_645_; 
v___x_631_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v___x_631_, 0, v_a_571_);
lean_ctor_set(v___x_631_, 1, v_a_611_);
lean_ctor_set(v___x_631_, 2, v_a_627_);
v___x_632_ = lean_unbox(v_a_575_);
lean_dec(v_a_575_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3, v___x_632_);
v___x_633_ = lean_unbox(v_a_579_);
lean_dec(v_a_579_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 1, v___x_633_);
v___x_634_ = lean_unbox(v_a_583_);
lean_dec(v_a_583_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 2, v___x_634_);
v___x_635_ = lean_unbox(v_a_587_);
lean_dec(v_a_587_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 3, v___x_635_);
v___x_636_ = lean_unbox(v_a_591_);
lean_dec(v_a_591_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 4, v___x_636_);
v___x_637_ = lean_unbox(v_a_595_);
lean_dec(v_a_595_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 5, v___x_637_);
v___x_638_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 6, v___x_638_);
v___x_639_ = lean_unbox(v_a_603_);
lean_dec(v_a_603_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 7, v___x_639_);
v___x_640_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 8, v___x_640_);
v___x_641_ = lean_unbox(v_a_615_);
lean_dec(v_a_615_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 9, v___x_641_);
v___x_642_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 10, v___x_642_);
v___x_643_ = lean_unbox(v_a_623_);
lean_dec(v_a_623_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 11, v___x_643_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_631_);
v___x_645_ = v___x_629_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_631_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_a_623_);
lean_dec(v_a_619_);
lean_dec(v_a_615_);
lean_dec(v_a_611_);
lean_dec(v_a_607_);
lean_dec(v_a_603_);
lean_dec(v_a_599_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_648_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_626_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_626_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_a_619_);
lean_dec(v_a_615_);
lean_dec(v_a_611_);
lean_dec(v_a_607_);
lean_dec(v_a_603_);
lean_dec(v_a_599_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_656_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_622_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_622_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
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
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_a_615_);
lean_dec(v_a_611_);
lean_dec(v_a_607_);
lean_dec(v_a_603_);
lean_dec(v_a_599_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_664_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_618_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_618_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
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
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec(v_a_611_);
lean_dec(v_a_607_);
lean_dec(v_a_603_);
lean_dec(v_a_599_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_672_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_614_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_614_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_a_607_);
lean_dec(v_a_603_);
lean_dec(v_a_599_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_680_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_610_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_610_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_a_603_);
lean_dec(v_a_599_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_688_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_606_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_606_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_a_599_);
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_696_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_602_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_602_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
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
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_a_595_);
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_704_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_598_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_598_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_a_591_);
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_712_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_594_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_594_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_a_587_);
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_720_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_590_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_590_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_a_583_);
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_728_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_586_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_586_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_a_579_);
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_736_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_582_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_582_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_575_);
lean_dec(v_a_571_);
v_a_744_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_578_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_578_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_571_);
v_a_752_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_574_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_574_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_570_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_570_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object* v___x_784_, lean_object* v_ctor_785_, lean_object* v_args_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(v___x_784_, v_ctor_785_, v_args_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v_args_786_);
lean_dec_ref(v_ctor_785_);
lean_dec_ref(v___x_784_);
return v_res_792_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_793_; lean_object* v___f_794_; 
v___x_793_ = l_Lean_instInhabitedExpr;
v___f_794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_794_, 0, v___x_793_);
return v___f_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___f_808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0);
v___x_809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_810_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_809_, v___f_808_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_817_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_box(0);
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_821_ = l_Lean_Expr_const___override(v___x_820_, v___x_819_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0));
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_824_);
return v___x_826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig(void){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v___x_829_ = l_Lean_Elab_abortTermExceptionId;
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg(){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v_res_835_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_box(1);
v___x_837_ = l_Lean_MessageData_ofFormat(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2));
v___x_842_ = l_Lean_MessageData_ofFormat(v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
if (lean_obj_tag(v_x_844_) == 0)
{
return v_x_843_;
}
else
{
lean_object* v_head_845_; lean_object* v_tail_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_868_; 
v_head_845_ = lean_ctor_get(v_x_844_, 0);
v_tail_846_ = lean_ctor_get(v_x_844_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x_844_);
if (v_isSharedCheck_868_ == 0)
{
v___x_848_ = v_x_844_;
v_isShared_849_ = v_isSharedCheck_868_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_tail_846_);
lean_inc(v_head_845_);
lean_dec(v_x_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_868_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_before_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_866_; 
v_before_850_ = lean_ctor_get(v_head_845_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_head_845_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_head_845_, 1);
lean_dec(v_unused_867_);
v___x_852_ = v_head_845_;
v_isShared_853_ = v_isSharedCheck_866_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_before_850_);
lean_dec(v_head_845_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_866_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 7);
lean_ctor_set(v___x_852_, 1, v___x_854_);
lean_ctor_set(v___x_852_, 0, v_x_843_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_x_843_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_865_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 7);
lean_ctor_set(v___x_848_, 1, v___x_857_);
lean_ctor_set(v___x_848_, 0, v___x_856_);
v___x_859_ = v___x_848_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_864_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = l_Lean_MessageData_ofSyntax(v_before_850_);
v___x_861_ = l_Lean_indentD(v___x_860_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_859_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v_x_843_ = v___x_862_;
v_x_844_ = v_tail_846_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object* v_opts_869_, lean_object* v_opt_870_){
_start:
{
lean_object* v_name_871_; lean_object* v_defValue_872_; lean_object* v_map_873_; lean_object* v___x_874_; 
v_name_871_ = lean_ctor_get(v_opt_870_, 0);
v_defValue_872_ = lean_ctor_get(v_opt_870_, 1);
v_map_873_ = lean_ctor_get(v_opts_869_, 0);
v___x_874_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_873_, v_name_871_);
if (lean_obj_tag(v___x_874_) == 0)
{
uint8_t v___x_875_; 
v___x_875_ = lean_unbox(v_defValue_872_);
return v___x_875_;
}
else
{
lean_object* v_val_876_; 
v_val_876_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v___x_874_, 1);
if (lean_obj_tag(v_val_876_) == 1)
{
uint8_t v_v_877_; 
v_v_877_ = lean_ctor_get_uint8(v_val_876_, 0);
lean_dec_ref_known(v_val_876_, 0);
return v_v_877_;
}
else
{
uint8_t v___x_878_; 
lean_dec(v_val_876_);
v___x_878_ = lean_unbox(v_defValue_872_);
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object* v_opts_879_, lean_object* v_opt_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_opts_879_, v_opt_880_);
lean_dec_ref(v_opt_880_);
lean_dec_ref(v_opts_879_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1));
v___x_887_ = l_Lean_MessageData_ofFormat(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object* v_msgData_888_, lean_object* v_macroStack_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_892_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_890_);
v___x_893_ = l_Lean_Elab_pp_macroStack;
v___x_894_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v___x_892_, v___x_893_);
lean_dec_ref(v___x_892_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v_macroStack_889_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_msgData_888_);
return v___x_895_;
}
else
{
if (lean_obj_tag(v_macroStack_889_) == 0)
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_msgData_888_);
return v___x_896_;
}
else
{
lean_object* v_head_897_; lean_object* v_after_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_913_; 
v_head_897_ = lean_ctor_get(v_macroStack_889_, 0);
lean_inc(v_head_897_);
v_after_898_ = lean_ctor_get(v_head_897_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_head_897_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v_head_897_, 0);
lean_dec(v_unused_914_);
v___x_900_ = v_head_897_;
v_isShared_901_ = v_isSharedCheck_913_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_after_898_);
lean_dec(v_head_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_913_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 7);
lean_ctor_set(v___x_900_, 1, v___x_902_);
lean_ctor_set(v___x_900_, 0, v_msgData_888_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_msgData_888_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_912_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_msgData_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_905_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_MessageData_ofSyntax(v_after_898_);
v___x_908_ = l_Lean_indentD(v___x_907_);
v_msgData_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_909_, 0, v___x_906_);
lean_ctor_set(v_msgData_909_, 1, v___x_908_);
v___x_910_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(v_msgData_909_, v_macroStack_889_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_msgData_915_, lean_object* v_macroStack_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_915_, v_macroStack_916_, v___y_917_);
lean_dec_ref(v___y_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object* v_msg_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_ref_928_; lean_object* v_macroStack_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_a_932_; lean_object* v___x_933_; lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_942_; 
v_ref_928_ = lean_ctor_get(v___y_925_, 2);
v_macroStack_929_ = lean_ctor_get(v___y_921_, 1);
v___x_930_ = l_Lean_Elab_getBetterRef(v_ref_928_, v_macroStack_929_);
v___x_931_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_920_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref(v___x_931_);
lean_inc(v_macroStack_929_);
v___x_933_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_a_932_, v_macroStack_929_, v___y_925_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_942_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_930_);
lean_ctor_set(v___x_938_, 1, v_a_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 1);
lean_ctor_set(v___x_936_, 0, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object* v_msg_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object* v_e_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Expr_hasMVar(v_e_952_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_e_952_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v_mctx_958_; lean_object* v___x_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_962_; lean_object* v_cache_963_; lean_object* v_zetaDeltaFVarIds_964_; lean_object* v_postponed_965_; lean_object* v_diag_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v___x_957_ = lean_st_ref_get(v___y_953_);
v_mctx_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_mctx_958_);
lean_dec(v___x_957_);
v___x_959_ = l_Lean_instantiateMVarsCore(v_mctx_958_, v_e_952_);
v_fst_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_snd_961_);
lean_dec_ref(v___x_959_);
v___x_962_ = lean_st_ref_take(v___y_953_);
v_cache_963_ = lean_ctor_get(v___x_962_, 1);
v_zetaDeltaFVarIds_964_ = lean_ctor_get(v___x_962_, 2);
v_postponed_965_ = lean_ctor_get(v___x_962_, 3);
v_diag_966_ = lean_ctor_get(v___x_962_, 4);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_976_);
v___x_968_ = v___x_962_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_diag_966_);
lean_inc(v_postponed_965_);
lean_inc(v_zetaDeltaFVarIds_964_);
lean_inc(v_cache_963_);
lean_dec(v___x_962_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_snd_961_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_snd_961_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_cache_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_zetaDeltaFVarIds_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_postponed_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_diag_966_);
v___x_971_ = v_reuseFailAlloc_974_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_st_ref_put(v___y_953_, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_fst_960_);
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object* v_e_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_977_, v___y_978_);
lean_dec(v___y_978_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_985_ = l_Lean_MessageData_ofExpr(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2);
v___x_987_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_993_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(lean_object* v_stx_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_ty_x3f_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_toCold_1015_; lean_object* v_currRecDepth_1016_; lean_object* v_ref_1017_; uint16_t v_optionFlags_1018_; uint8_t v_suppressElabErrors_1019_; uint8_t v_isRecordingDeps_1020_; uint8_t v___x_1021_; lean_object* v_ref_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_ty_x3f_1009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_1010_ = 1;
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_box(v___x_1010_);
v___x_1013_ = lean_box(v___x_1010_);
lean_inc(v_stx_1001_);
v___x_1014_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1014_, 0, v_stx_1001_);
lean_closure_set(v___x_1014_, 1, v_ty_x3f_1009_);
lean_closure_set(v___x_1014_, 2, v___x_1012_);
lean_closure_set(v___x_1014_, 3, v___x_1013_);
lean_closure_set(v___x_1014_, 4, v___x_1011_);
v_toCold_1015_ = lean_ctor_get(v_a_1006_, 0);
v_currRecDepth_1016_ = lean_ctor_get(v_a_1006_, 1);
v_ref_1017_ = lean_ctor_get(v_a_1006_, 2);
v_optionFlags_1018_ = lean_ctor_get_uint16(v_a_1006_, sizeof(void*)*3);
v_suppressElabErrors_1019_ = lean_ctor_get_uint8(v_a_1006_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1020_ = lean_ctor_get_uint8(v_a_1006_, sizeof(void*)*3 + 3);
v___x_1021_ = 1;
v_ref_1022_ = l_Lean_replaceRef(v_stx_1001_, v_ref_1017_);
lean_dec(v_stx_1001_);
lean_inc(v_currRecDepth_1016_);
lean_inc_ref(v_toCold_1015_);
v___x_1023_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1023_, 0, v_toCold_1015_);
lean_ctor_set(v___x_1023_, 1, v_currRecDepth_1016_);
lean_ctor_set(v___x_1023_, 2, v_ref_1022_);
lean_ctor_set_uint16(v___x_1023_, sizeof(void*)*3, v_optionFlags_1018_);
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*3 + 2, v_suppressElabErrors_1019_);
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*3 + 3, v_isRecordingDeps_1020_);
v___x_1024_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1014_, v___x_1021_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v___x_1023_, v_a_1007_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; uint8_t v___y_1038_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; uint8_t v___x_1122_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1025_, v_a_1005_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1122_ = l_Lean_Expr_hasSorry(v_a_1027_);
if (v___x_1122_ == 0)
{
v___y_1067_ = v_a_1002_;
v___y_1068_ = v_a_1003_;
v___y_1069_ = v_a_1004_;
v___y_1070_ = v_a_1005_;
v___y_1071_ = v___x_1023_;
v___y_1072_ = v_a_1007_;
goto v___jp_1066_;
}
else
{
uint8_t v___x_1123_; 
v___x_1123_ = l_Lean_Expr_hasSyntheticSorry(v_a_1027_);
if (v___x_1123_ == 0)
{
v___y_1104_ = v_a_1002_;
v___y_1105_ = v_a_1003_;
v___y_1106_ = v_a_1004_;
v___y_1107_ = v_a_1005_;
v___y_1108_ = v___x_1023_;
v___y_1109_ = v_a_1007_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1124_; lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_a_1027_);
lean_dec_ref_known(v___x_1023_, 3);
v___x_1124_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
v___jp_1028_:
{
if (v___y_1038_ == 0)
{
if (lean_obj_tag(v___y_1031_) == 0)
{
lean_dec_ref_known(v___y_1031_, 2);
lean_dec_ref(v___y_1033_);
lean_dec(v_a_1027_);
return v___y_1030_;
}
else
{
lean_object* v_id_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1052_; 
v_id_1039_ = lean_ctor_get(v___y_1031_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___y_1031_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___y_1031_, 1);
lean_dec(v_unused_1053_);
v___x_1041_ = v___y_1031_;
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_id_1039_);
lean_dec(v___y_1031_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1052_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
uint8_t v___x_1043_; 
v___x_1043_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1029_, v_id_1039_);
lean_dec(v_id_1039_);
if (v___x_1043_ == 0)
{
lean_del_object(v___x_1041_);
lean_dec_ref(v___y_1033_);
lean_dec(v_a_1027_);
return v___y_1030_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_dec_ref(v___y_1030_);
v___x_1044_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6);
v___x_1045_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1046_ = l_Lean_indentExpr(v_a_1027_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 7);
lean_ctor_set(v___x_1041_, 1, v___x_1046_);
lean_ctor_set(v___x_1041_, 0, v___x_1045_);
v___x_1048_ = v___x_1041_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1044_);
v___x_1050_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1049_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1034_, v___y_1033_, v___y_1032_);
lean_dec_ref(v___y_1033_);
return v___x_1050_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1033_);
lean_dec_ref(v___y_1031_);
lean_dec(v_a_1027_);
return v___y_1030_;
}
}
v___jp_1054_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1027_);
v___x_1062_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_1027_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_dec_ref(v___y_1059_);
lean_dec(v_a_1027_);
return v___x_1062_;
}
else
{
lean_object* v_a_1063_; uint8_t v___x_1064_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
v___x_1064_ = l_Lean_Exception_isInterrupt(v_a_1063_);
if (v___x_1064_ == 0)
{
uint8_t v___x_1065_; 
lean_inc(v_a_1063_);
v___x_1065_ = l_Lean_Exception_isRuntime(v_a_1063_);
v___y_1029_ = v___x_1061_;
v___y_1030_ = v___x_1062_;
v___y_1031_ = v_a_1063_;
v___y_1032_ = v___y_1060_;
v___y_1033_ = v___y_1059_;
v___y_1034_ = v___y_1058_;
v___y_1035_ = v___y_1055_;
v___y_1036_ = v___y_1056_;
v___y_1037_ = v___y_1057_;
v___y_1038_ = v___x_1065_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___x_1061_;
v___y_1030_ = v___x_1062_;
v___y_1031_ = v_a_1063_;
v___y_1032_ = v___y_1060_;
v___y_1033_ = v___y_1059_;
v___y_1034_ = v___y_1058_;
v___y_1035_ = v___y_1055_;
v___y_1036_ = v___y_1056_;
v___y_1037_ = v___y_1057_;
v___y_1038_ = v___x_1064_;
goto v___jp_1028_;
}
}
}
v___jp_1066_:
{
lean_object* v___x_1073_; 
lean_inc(v_a_1027_);
v___x_1073_ = l_Lean_Meta_getMVars(v_a_1027_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1075_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1075_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1074_, v___x_1011_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v_a_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; uint8_t v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = lean_unbox(v_a_1076_);
lean_dec(v_a_1076_);
if (v___x_1077_ == 0)
{
v___y_1055_ = v___y_1067_;
v___y_1056_ = v___y_1068_;
v___y_1057_ = v___y_1069_;
v___y_1058_ = v___y_1070_;
v___y_1059_ = v___y_1071_;
v___y_1060_ = v___y_1072_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v___y_1071_);
lean_dec(v_a_1027_);
v___x_1078_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v___y_1071_);
lean_dec(v_a_1027_);
v_a_1087_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1075_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1075_);
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
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v___y_1071_);
lean_dec(v_a_1027_);
v_a_1095_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1073_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1073_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
v___jp_1103_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v___x_1110_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1111_ = l_Lean_indentExpr(v_a_1027_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1112_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec_ref(v___y_1108_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref_known(v___x_1023_, 3);
v_a_1133_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1024_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1024_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_stx_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1149_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_1151_ = l_Lean_MessageData_ofExpr(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0);
v___x_1153_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1156_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_ty_x3f_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_toCold_1172_; lean_object* v_currRecDepth_1173_; lean_object* v_ref_1174_; uint16_t v_optionFlags_1175_; uint8_t v_suppressElabErrors_1176_; uint8_t v_isRecordingDeps_1177_; uint8_t v___x_1178_; lean_object* v_ref_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_ty_x3f_1166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_1167_ = 1;
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_box(v___x_1167_);
v___x_1170_ = lean_box(v___x_1167_);
lean_inc(v_stx_1158_);
v___x_1171_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1171_, 0, v_stx_1158_);
lean_closure_set(v___x_1171_, 1, v_ty_x3f_1166_);
lean_closure_set(v___x_1171_, 2, v___x_1169_);
lean_closure_set(v___x_1171_, 3, v___x_1170_);
lean_closure_set(v___x_1171_, 4, v___x_1168_);
v_toCold_1172_ = lean_ctor_get(v_a_1163_, 0);
v_currRecDepth_1173_ = lean_ctor_get(v_a_1163_, 1);
v_ref_1174_ = lean_ctor_get(v_a_1163_, 2);
v_optionFlags_1175_ = lean_ctor_get_uint16(v_a_1163_, sizeof(void*)*3);
v_suppressElabErrors_1176_ = lean_ctor_get_uint8(v_a_1163_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1177_ = lean_ctor_get_uint8(v_a_1163_, sizeof(void*)*3 + 3);
v___x_1178_ = 1;
v_ref_1179_ = l_Lean_replaceRef(v_stx_1158_, v_ref_1174_);
lean_dec(v_stx_1158_);
lean_inc(v_currRecDepth_1173_);
lean_inc_ref(v_toCold_1172_);
v___x_1180_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1180_, 0, v_toCold_1172_);
lean_ctor_set(v___x_1180_, 1, v_currRecDepth_1173_);
lean_ctor_set(v___x_1180_, 2, v_ref_1179_);
lean_ctor_set_uint16(v___x_1180_, sizeof(void*)*3, v_optionFlags_1175_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*3 + 2, v_suppressElabErrors_1176_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*3 + 3, v_isRecordingDeps_1177_);
v___x_1181_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1171_, v___x_1178_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v___x_1180_, v_a_1164_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; lean_object* v_a_1184_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; uint8_t v___y_1195_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; uint8_t v___x_1279_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1182_, v_a_1162_);
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref(v___x_1183_);
v___x_1279_ = l_Lean_Expr_hasSorry(v_a_1184_);
if (v___x_1279_ == 0)
{
v___y_1224_ = v_a_1159_;
v___y_1225_ = v_a_1160_;
v___y_1226_ = v_a_1161_;
v___y_1227_ = v_a_1162_;
v___y_1228_ = v___x_1180_;
v___y_1229_ = v_a_1164_;
goto v___jp_1223_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = l_Lean_Expr_hasSyntheticSorry(v_a_1184_);
if (v___x_1280_ == 0)
{
v___y_1261_ = v_a_1159_;
v___y_1262_ = v_a_1160_;
v___y_1263_ = v_a_1161_;
v___y_1264_ = v_a_1162_;
v___y_1265_ = v___x_1180_;
v___y_1266_ = v_a_1164_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1281_; lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_a_1184_);
lean_dec_ref_known(v___x_1180_, 3);
v___x_1281_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
v___jp_1185_:
{
if (v___y_1195_ == 0)
{
if (lean_obj_tag(v___y_1191_) == 0)
{
lean_dec_ref_known(v___y_1191_, 2);
lean_dec_ref(v___y_1192_);
lean_dec(v_a_1184_);
return v___y_1186_;
}
else
{
lean_object* v_id_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1209_; 
v_id_1196_ = lean_ctor_get(v___y_1191_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___y_1191_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___y_1191_, 1);
lean_dec(v_unused_1210_);
v___x_1198_ = v___y_1191_;
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_id_1196_);
lean_dec(v___y_1191_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1209_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1194_, v_id_1196_);
lean_dec(v_id_1196_);
if (v___x_1200_ == 0)
{
lean_del_object(v___x_1198_);
lean_dec_ref(v___y_1192_);
lean_dec(v_a_1184_);
return v___y_1186_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_dec_ref(v___y_1186_);
v___x_1201_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_1202_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1203_ = l_Lean_indentExpr(v_a_1184_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 7);
lean_ctor_set(v___x_1198_, 1, v___x_1203_);
lean_ctor_set(v___x_1198_, 0, v___x_1202_);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1201_);
v___x_1207_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1206_, v___y_1189_, v___y_1188_, v___y_1190_, v___y_1187_, v___y_1192_, v___y_1193_);
lean_dec_ref(v___y_1192_);
return v___x_1207_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v_a_1184_);
return v___y_1186_;
}
}
v___jp_1211_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1184_);
v___x_1219_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_1184_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_dec_ref(v___y_1216_);
lean_dec(v_a_1184_);
return v___x_1219_;
}
else
{
lean_object* v_a_1220_; uint8_t v___x_1221_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
v___x_1221_ = l_Lean_Exception_isInterrupt(v_a_1220_);
if (v___x_1221_ == 0)
{
uint8_t v___x_1222_; 
lean_inc(v_a_1220_);
v___x_1222_ = l_Lean_Exception_isRuntime(v_a_1220_);
v___y_1186_ = v___x_1219_;
v___y_1187_ = v___y_1215_;
v___y_1188_ = v___y_1213_;
v___y_1189_ = v___y_1212_;
v___y_1190_ = v___y_1214_;
v___y_1191_ = v_a_1220_;
v___y_1192_ = v___y_1216_;
v___y_1193_ = v___y_1217_;
v___y_1194_ = v___x_1218_;
v___y_1195_ = v___x_1222_;
goto v___jp_1185_;
}
else
{
v___y_1186_ = v___x_1219_;
v___y_1187_ = v___y_1215_;
v___y_1188_ = v___y_1213_;
v___y_1189_ = v___y_1212_;
v___y_1190_ = v___y_1214_;
v___y_1191_ = v_a_1220_;
v___y_1192_ = v___y_1216_;
v___y_1193_ = v___y_1217_;
v___y_1194_ = v___x_1218_;
v___y_1195_ = v___x_1221_;
goto v___jp_1185_;
}
}
}
v___jp_1223_:
{
lean_object* v___x_1230_; 
lean_inc(v_a_1184_);
v___x_1230_ = l_Lean_Meta_getMVars(v_a_1184_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1232_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
lean_dec_ref_known(v___x_1230_, 1);
v___x_1232_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1231_, v___x_1168_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v_a_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; uint8_t v___x_1234_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = lean_unbox(v_a_1233_);
lean_dec(v_a_1233_);
if (v___x_1234_ == 0)
{
v___y_1212_ = v___y_1224_;
v___y_1213_ = v___y_1225_;
v___y_1214_ = v___y_1226_;
v___y_1215_ = v___y_1227_;
v___y_1216_ = v___y_1228_;
v___y_1217_ = v___y_1229_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1235_; lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec_ref(v___y_1228_);
lean_dec(v_a_1184_);
v___x_1235_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v___y_1228_);
lean_dec(v_a_1184_);
v_a_1244_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1232_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1232_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v___y_1228_);
lean_dec(v_a_1184_);
v_a_1252_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1230_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1230_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
v___jp_1260_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v___x_1267_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1268_ = l_Lean_indentExpr(v_a_1184_);
v___x_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1269_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec_ref(v___y_1265_);
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref_known(v___x_1180_, 3);
v_a_1290_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1181_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1181_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(lean_object* v_stx_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_toCold_1315_; lean_object* v_currRecDepth_1316_; lean_object* v_ref_1317_; uint16_t v_optionFlags_1318_; uint8_t v_suppressElabErrors_1319_; uint8_t v_isRecordingDeps_1320_; lean_object* v___x_1321_; lean_object* v_ref_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_toCold_1315_ = lean_ctor_get(v_a_1312_, 0);
v_currRecDepth_1316_ = lean_ctor_get(v_a_1312_, 1);
v_ref_1317_ = lean_ctor_get(v_a_1312_, 2);
v_optionFlags_1318_ = lean_ctor_get_uint16(v_a_1312_, sizeof(void*)*3);
v_suppressElabErrors_1319_ = lean_ctor_get_uint8(v_a_1312_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1320_ = lean_ctor_get_uint8(v_a_1312_, sizeof(void*)*3 + 3);
v___x_1321_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1322_ = l_Lean_replaceRef(v_stx_1307_, v_ref_1317_);
lean_inc(v_currRecDepth_1316_);
lean_inc_ref(v_toCold_1315_);
v___x_1323_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1323_, 0, v_toCold_1315_);
lean_ctor_set(v___x_1323_, 1, v_currRecDepth_1316_);
lean_ctor_set(v___x_1323_, 2, v_ref_1322_);
lean_ctor_set_uint16(v___x_1323_, sizeof(void*)*3, v_optionFlags_1318_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*3 + 2, v_suppressElabErrors_1319_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*3 + 3, v_isRecordingDeps_1320_);
lean_inc(v_stx_1307_);
v___x_1324_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_stx_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v___x_1323_, v_a_1313_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref_known(v___x_1323_, 3);
lean_dec(v_stx_1307_);
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
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1348_; 
v_a_1334_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1336_ = v___x_1324_;
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1324_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
lean_inc(v_a_1334_);
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
uint8_t v___y_1341_; uint8_t v___x_1345_; 
v___x_1345_ = l_Lean_Exception_isInterrupt(v_a_1334_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; 
lean_inc(v_a_1334_);
v___x_1346_ = l_Lean_Exception_isRuntime(v_a_1334_);
v___y_1341_ = v___x_1346_;
goto v___jp_1340_;
}
else
{
v___y_1341_ = v___x_1345_;
goto v___jp_1340_;
}
v___jp_1340_:
{
if (v___y_1341_ == 0)
{
if (lean_obj_tag(v_a_1334_) == 0)
{
lean_dec_ref_known(v_a_1334_, 2);
lean_dec_ref_known(v___x_1323_, 3);
lean_dec(v_stx_1307_);
return v___x_1339_;
}
else
{
lean_object* v_id_1342_; uint8_t v___x_1343_; 
v_id_1342_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_id_1342_);
lean_dec_ref_known(v_a_1334_, 2);
v___x_1343_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1321_, v_id_1342_);
lean_dec(v_id_1342_);
if (v___x_1343_ == 0)
{
lean_dec_ref_known(v___x_1323_, 3);
lean_dec(v_stx_1307_);
return v___x_1339_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1339_);
v___x_1344_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v___x_1323_, v_a_1313_);
lean_dec_ref_known(v___x_1323_, 3);
return v___x_1344_;
}
}
}
else
{
lean_dec(v_a_1334_);
lean_dec_ref_known(v___x_1323_, 3);
lean_dec(v_stx_1307_);
return v___x_1339_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_stx_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1357_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_box(0);
v___x_1362_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_1363_ = l_Lean_mkConst(v___x_1362_, v___x_1361_);
return v___x_1363_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1364_; lean_object* v_ty_x3f_1365_; 
v___x_1364_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_1365_, 0, v___x_1364_);
return v_ty_x3f_1365_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_1367_ = l_Lean_MessageData_ofExpr(v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_1369_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v___x_1368_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1372_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___x_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_ty_x3f_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_toCold_1388_; lean_object* v_currRecDepth_1389_; lean_object* v_ref_1390_; uint16_t v_optionFlags_1391_; uint8_t v_suppressElabErrors_1392_; uint8_t v_isRecordingDeps_1393_; uint8_t v___x_1394_; lean_object* v_ref_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_ty_x3f_1382_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_1383_ = 1;
v___x_1384_ = lean_box(0);
v___x_1385_ = lean_box(v___x_1383_);
v___x_1386_ = lean_box(v___x_1383_);
lean_inc(v_stx_1374_);
v___x_1387_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1387_, 0, v_stx_1374_);
lean_closure_set(v___x_1387_, 1, v_ty_x3f_1382_);
lean_closure_set(v___x_1387_, 2, v___x_1385_);
lean_closure_set(v___x_1387_, 3, v___x_1386_);
lean_closure_set(v___x_1387_, 4, v___x_1384_);
v_toCold_1388_ = lean_ctor_get(v_a_1379_, 0);
v_currRecDepth_1389_ = lean_ctor_get(v_a_1379_, 1);
v_ref_1390_ = lean_ctor_get(v_a_1379_, 2);
v_optionFlags_1391_ = lean_ctor_get_uint16(v_a_1379_, sizeof(void*)*3);
v_suppressElabErrors_1392_ = lean_ctor_get_uint8(v_a_1379_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1393_ = lean_ctor_get_uint8(v_a_1379_, sizeof(void*)*3 + 3);
v___x_1394_ = 1;
v_ref_1395_ = l_Lean_replaceRef(v_stx_1374_, v_ref_1390_);
lean_dec(v_stx_1374_);
lean_inc(v_currRecDepth_1389_);
lean_inc_ref(v_toCold_1388_);
v___x_1396_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1396_, 0, v_toCold_1388_);
lean_ctor_set(v___x_1396_, 1, v_currRecDepth_1389_);
lean_ctor_set(v___x_1396_, 2, v_ref_1395_);
lean_ctor_set_uint16(v___x_1396_, sizeof(void*)*3, v_optionFlags_1391_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*3 + 2, v_suppressElabErrors_1392_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*3 + 3, v_isRecordingDeps_1393_);
v___x_1397_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1387_, v___x_1394_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v___x_1396_, v_a_1380_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; lean_object* v_a_1400_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; uint8_t v___y_1411_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; uint8_t v___x_1495_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1398_, v_a_1378_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1399_);
v___x_1495_ = l_Lean_Expr_hasSorry(v_a_1400_);
if (v___x_1495_ == 0)
{
v___y_1440_ = v_a_1375_;
v___y_1441_ = v_a_1376_;
v___y_1442_ = v_a_1377_;
v___y_1443_ = v_a_1378_;
v___y_1444_ = v___x_1396_;
v___y_1445_ = v_a_1380_;
goto v___jp_1439_;
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = l_Lean_Expr_hasSyntheticSorry(v_a_1400_);
if (v___x_1496_ == 0)
{
v___y_1477_ = v_a_1375_;
v___y_1478_ = v_a_1376_;
v___y_1479_ = v_a_1377_;
v___y_1480_ = v_a_1378_;
v___y_1481_ = v___x_1396_;
v___y_1482_ = v_a_1380_;
goto v___jp_1476_;
}
else
{
lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1400_);
lean_dec_ref_known(v___x_1396_, 3);
v___x_1497_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
v___jp_1401_:
{
if (v___y_1411_ == 0)
{
if (lean_obj_tag(v___y_1403_) == 0)
{
lean_dec_ref_known(v___y_1403_, 2);
lean_dec_ref(v___y_1408_);
lean_dec(v_a_1400_);
return v___y_1404_;
}
else
{
lean_object* v_id_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1425_; 
v_id_1412_ = lean_ctor_get(v___y_1403_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___y_1403_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___y_1403_, 1);
lean_dec(v_unused_1426_);
v___x_1414_ = v___y_1403_;
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_id_1412_);
lean_dec(v___y_1403_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
uint8_t v___x_1416_; 
v___x_1416_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1410_, v_id_1412_);
lean_dec(v_id_1412_);
if (v___x_1416_ == 0)
{
lean_del_object(v___x_1414_);
lean_dec_ref(v___y_1408_);
lean_dec(v_a_1400_);
return v___y_1404_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
lean_dec_ref(v___y_1404_);
v___x_1417_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_1418_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1419_ = l_Lean_indentExpr(v_a_1400_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set_tag(v___x_1414_, 7);
lean_ctor_set(v___x_1414_, 1, v___x_1419_);
lean_ctor_set(v___x_1414_, 0, v___x_1418_);
v___x_1421_ = v___x_1414_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v___x_1417_);
v___x_1423_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1422_, v___y_1406_, v___y_1405_, v___y_1402_, v___y_1409_, v___y_1408_, v___y_1407_);
lean_dec_ref(v___y_1408_);
return v___x_1423_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1408_);
lean_dec_ref(v___y_1403_);
lean_dec(v_a_1400_);
return v___y_1404_;
}
}
v___jp_1427_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1400_);
v___x_1435_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_a_1400_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref(v___y_1432_);
lean_dec(v_a_1400_);
return v___x_1435_;
}
else
{
lean_object* v_a_1436_; uint8_t v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
v___x_1437_ = l_Lean_Exception_isInterrupt(v_a_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; 
lean_inc(v_a_1436_);
v___x_1438_ = l_Lean_Exception_isRuntime(v_a_1436_);
v___y_1402_ = v___y_1430_;
v___y_1403_ = v_a_1436_;
v___y_1404_ = v___x_1435_;
v___y_1405_ = v___y_1429_;
v___y_1406_ = v___y_1428_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v___y_1431_;
v___y_1410_ = v___x_1434_;
v___y_1411_ = v___x_1438_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___y_1430_;
v___y_1403_ = v_a_1436_;
v___y_1404_ = v___x_1435_;
v___y_1405_ = v___y_1429_;
v___y_1406_ = v___y_1428_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v___y_1431_;
v___y_1410_ = v___x_1434_;
v___y_1411_ = v___x_1437_;
goto v___jp_1401_;
}
}
}
v___jp_1439_:
{
lean_object* v___x_1446_; 
lean_inc(v_a_1400_);
v___x_1446_ = l_Lean_Meta_getMVars(v_a_1400_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1447_, v___x_1384_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v_a_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; uint8_t v___x_1450_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = lean_unbox(v_a_1449_);
lean_dec(v_a_1449_);
if (v___x_1450_ == 0)
{
v___y_1428_ = v___y_1440_;
v___y_1429_ = v___y_1441_;
v___y_1430_ = v___y_1442_;
v___y_1431_ = v___y_1443_;
v___y_1432_ = v___y_1444_;
v___y_1433_ = v___y_1445_;
goto v___jp_1427_;
}
else
{
lean_object* v___x_1451_; lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v___y_1444_);
lean_dec(v_a_1400_);
v___x_1451_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v___y_1444_);
lean_dec(v_a_1400_);
v_a_1460_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1448_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1448_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v___y_1444_);
lean_dec(v_a_1400_);
v_a_1468_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1446_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1446_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
v___jp_1476_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v___x_1483_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1484_ = l_Lean_indentExpr(v_a_1400_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1485_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec_ref(v___y_1481_);
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
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref_known(v___x_1396_, 3);
v_a_1506_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1397_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1397_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_toCold_1531_; lean_object* v_currRecDepth_1532_; lean_object* v_ref_1533_; uint16_t v_optionFlags_1534_; uint8_t v_suppressElabErrors_1535_; uint8_t v_isRecordingDeps_1536_; lean_object* v___x_1537_; lean_object* v_ref_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_toCold_1531_ = lean_ctor_get(v_a_1528_, 0);
v_currRecDepth_1532_ = lean_ctor_get(v_a_1528_, 1);
v_ref_1533_ = lean_ctor_get(v_a_1528_, 2);
v_optionFlags_1534_ = lean_ctor_get_uint16(v_a_1528_, sizeof(void*)*3);
v_suppressElabErrors_1535_ = lean_ctor_get_uint8(v_a_1528_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1536_ = lean_ctor_get_uint8(v_a_1528_, sizeof(void*)*3 + 3);
v___x_1537_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1538_ = l_Lean_replaceRef(v_stx_1523_, v_ref_1533_);
lean_inc(v_currRecDepth_1532_);
lean_inc_ref(v_toCold_1531_);
v___x_1539_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1539_, 0, v_toCold_1531_);
lean_ctor_set(v___x_1539_, 1, v_currRecDepth_1532_);
lean_ctor_set(v___x_1539_, 2, v_ref_1538_);
lean_ctor_set_uint16(v___x_1539_, sizeof(void*)*3, v_optionFlags_1534_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*3 + 2, v_suppressElabErrors_1535_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*3 + 3, v_isRecordingDeps_1536_);
lean_inc(v_stx_1523_);
v___x_1540_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v___x_1539_, v_a_1529_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref_known(v___x_1539_, 3);
lean_dec(v_stx_1523_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_fst_1545_; lean_object* v___x_1547_; 
v_fst_1545_ = lean_ctor_get(v_a_1541_, 0);
lean_inc(v_fst_1545_);
lean_dec(v_a_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v_fst_1545_);
v___x_1547_ = v___x_1543_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_fst_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1564_; 
v_a_1550_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1552_ = v___x_1540_;
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1540_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1564_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
lean_inc(v_a_1550_);
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
uint8_t v___y_1557_; uint8_t v___x_1561_; 
v___x_1561_ = l_Lean_Exception_isInterrupt(v_a_1550_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; 
lean_inc(v_a_1550_);
v___x_1562_ = l_Lean_Exception_isRuntime(v_a_1550_);
v___y_1557_ = v___x_1562_;
goto v___jp_1556_;
}
else
{
v___y_1557_ = v___x_1561_;
goto v___jp_1556_;
}
v___jp_1556_:
{
if (v___y_1557_ == 0)
{
if (lean_obj_tag(v_a_1550_) == 0)
{
lean_dec_ref_known(v_a_1550_, 2);
lean_dec_ref_known(v___x_1539_, 3);
lean_dec(v_stx_1523_);
return v___x_1555_;
}
else
{
lean_object* v_id_1558_; uint8_t v___x_1559_; 
v_id_1558_ = lean_ctor_get(v_a_1550_, 0);
lean_inc(v_id_1558_);
lean_dec_ref_known(v_a_1550_, 2);
v___x_1559_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1537_, v_id_1558_);
lean_dec(v_id_1558_);
if (v___x_1559_ == 0)
{
lean_dec_ref_known(v___x_1539_, 3);
lean_dec(v_stx_1523_);
return v___x_1555_;
}
else
{
lean_object* v___x_1560_; 
lean_dec_ref(v___x_1555_);
v___x_1560_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v___x_1539_, v_a_1529_);
lean_dec_ref_known(v___x_1539_, 3);
return v___x_1560_;
}
}
}
else
{
lean_dec(v_a_1550_);
lean_dec_ref_known(v___x_1539_, 3);
lean_dec(v_stx_1523_);
return v___x_1555_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_stx_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(lean_object* v_config_1696_, lean_object* v_item_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_item_1706_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_1710_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1697_, v___x_1709_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1710_) == 0)
{
uint8_t v___x_1711_; 
lean_dec_ref_known(v___x_1710_, 1);
v___x_1711_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1697_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1712_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1697_);
lean_inc_ref(v_item_1697_);
v___x_1713_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1697_);
v___x_1714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_1715_ = lean_string_dec_lt(v___x_1712_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_1717_ = lean_string_dec_lt(v___x_1712_, v___x_1716_);
if (v___x_1717_ == 0)
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_string_dec_eq(v___x_1712_, v___x_1716_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_1720_ = lean_string_dec_eq(v___x_1712_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_1722_ = lean_string_dec_eq(v___x_1712_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_));
v___x_1724_ = lean_string_dec_eq(v___x_1712_, v___x_1723_);
lean_dec_ref(v___x_1712_);
if (v___x_1724_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_1726_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_1725_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1726_) == 0)
{
uint8_t v___x_1727_; 
lean_dec_ref_known(v___x_1726_, 1);
v___x_1727_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_1727_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1728_; 
lean_dec_ref(v___x_1713_);
v___x_1728_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1758_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1758_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1758_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_timeout_1733_; uint8_t v_trimProofs_1734_; uint8_t v_binaryProofs_1735_; uint8_t v_acNf_1736_; uint8_t v_andFlattening_1737_; uint8_t v_embeddedConstraintSubst_1738_; uint8_t v_structures_1739_; uint8_t v_fixedInt_1740_; uint8_t v_enums_1741_; uint8_t v_graphviz_1742_; lean_object* v_maxSteps_1743_; uint8_t v_shortCircuit_1744_; uint8_t v_solverMode_1745_; lean_object* v_cegarRounds_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1757_; 
v_timeout_1733_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_1734_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_1735_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_1736_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_1737_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1738_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_1739_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_1740_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_1741_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_1742_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_1743_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_1744_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_1745_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_cegarRounds_1746_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1748_ = v_config_1696_;
v_isShared_1749_ = v_isSharedCheck_1757_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_cegarRounds_1746_);
lean_inc(v_maxSteps_1743_);
lean_inc(v_timeout_1733_);
lean_dec(v_config_1696_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1757_;
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
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_timeout_1733_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_maxSteps_1743_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_cegarRounds_1746_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3, v_trimProofs_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 1, v_binaryProofs_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 2, v_acNf_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 3, v_andFlattening_1737_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 5, v_structures_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 6, v_fixedInt_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 7, v_enums_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 8, v_graphviz_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 9, v_shortCircuit_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 10, v_solverMode_1745_);
v___x_1751_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
uint8_t v___x_1752_; lean_object* v___x_1754_; 
v___x_1752_ = lean_unbox(v_a_1729_);
lean_dec(v_a_1729_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 11, v___x_1752_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1751_);
v___x_1754_ = v___x_1731_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1751_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref(v_config_1696_);
v_a_1759_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1728_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1728_);
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
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_1767_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1726_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1726_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec_ref(v___x_1712_);
v___x_1775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_1776_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_1775_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1776_) == 0)
{
uint8_t v___x_1777_; 
lean_dec_ref_known(v___x_1776_, 1);
v___x_1777_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1778_; 
lean_dec_ref(v___x_1713_);
v___x_1778_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1808_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1808_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1808_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_timeout_1783_; uint8_t v_binaryProofs_1784_; uint8_t v_acNf_1785_; uint8_t v_andFlattening_1786_; uint8_t v_embeddedConstraintSubst_1787_; uint8_t v_structures_1788_; uint8_t v_fixedInt_1789_; uint8_t v_enums_1790_; uint8_t v_graphviz_1791_; lean_object* v_maxSteps_1792_; uint8_t v_shortCircuit_1793_; uint8_t v_solverMode_1794_; uint8_t v_uf_1795_; lean_object* v_cegarRounds_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1807_; 
v_timeout_1783_ = lean_ctor_get(v_config_1696_, 0);
v_binaryProofs_1784_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_1785_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_1786_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1787_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_1788_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_1789_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_1790_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_1791_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_1792_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_1793_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_1794_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_1795_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_1796_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1798_ = v_config_1696_;
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_cegarRounds_1796_);
lean_inc(v_maxSteps_1792_);
lean_inc(v_timeout_1783_);
lean_dec(v_config_1696_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1807_;
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
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_timeout_1783_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_maxSteps_1792_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_cegarRounds_1796_);
v___x_1801_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
uint8_t v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_unbox(v_a_1779_);
lean_dec(v_a_1779_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3, v___x_1802_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 1, v_binaryProofs_1784_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 2, v_acNf_1785_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 3, v_andFlattening_1786_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1787_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 5, v_structures_1788_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 6, v_fixedInt_1789_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 7, v_enums_1790_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 8, v_graphviz_1791_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 9, v_shortCircuit_1793_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 10, v_solverMode_1794_);
lean_ctor_set_uint8(v___x_1801_, sizeof(void*)*3 + 11, v_uf_1795_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1801_);
v___x_1804_ = v___x_1781_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1801_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v_config_1696_);
v_a_1809_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1778_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1778_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_1817_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1776_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1776_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec_ref(v___x_1712_);
v___x_1825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_1826_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_1825_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1826_) == 0)
{
uint8_t v___x_1827_; 
lean_dec_ref_known(v___x_1826_, 1);
v___x_1827_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_1827_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1828_; 
lean_dec_ref(v___x_1713_);
lean_inc_ref(v_item_1697_);
v___x_1828_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_value_1829_; lean_object* v___x_1830_; 
lean_dec_ref_known(v___x_1828_, 1);
v_value_1829_ = lean_ctor_get(v_item_1697_, 2);
lean_inc(v_value_1829_);
lean_dec_ref(v_item_1697_);
v___x_1830_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1829_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1860_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1860_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1860_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
uint8_t v_trimProofs_1835_; uint8_t v_binaryProofs_1836_; uint8_t v_acNf_1837_; uint8_t v_andFlattening_1838_; uint8_t v_embeddedConstraintSubst_1839_; uint8_t v_structures_1840_; uint8_t v_fixedInt_1841_; uint8_t v_enums_1842_; uint8_t v_graphviz_1843_; lean_object* v_maxSteps_1844_; uint8_t v_shortCircuit_1845_; uint8_t v_solverMode_1846_; uint8_t v_uf_1847_; lean_object* v_cegarRounds_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1858_; 
v_trimProofs_1835_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_1836_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_1837_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_1838_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1839_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_1840_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_1841_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_1842_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_1843_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_1844_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_1845_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_1846_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_1847_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_1848_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_config_1696_, 0);
lean_dec(v_unused_1859_);
v___x_1850_ = v_config_1696_;
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_cegarRounds_1848_);
lean_inc(v_maxSteps_1844_);
lean_dec(v_config_1696_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_a_1831_);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1831_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_maxSteps_1844_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_cegarRounds_1848_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3, v_trimProofs_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 1, v_binaryProofs_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 2, v_acNf_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 3, v_andFlattening_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 5, v_structures_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 6, v_fixedInt_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 7, v_enums_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 8, v_graphviz_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 9, v_shortCircuit_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 10, v_solverMode_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*3 + 11, v_uf_1847_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1853_);
v___x_1855_ = v___x_1833_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
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
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_config_1696_);
v_a_1861_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1830_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1830_);
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
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_1869_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1828_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1828_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_1877_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1826_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1826_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref(v___x_1712_);
v___x_1885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_1886_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_1885_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1886_) == 0)
{
uint8_t v___x_1887_; 
lean_dec_ref_known(v___x_1886_, 1);
v___x_1887_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_1887_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1888_; 
lean_dec_ref(v___x_1713_);
v___x_1888_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1918_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1918_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1918_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_timeout_1893_; uint8_t v_trimProofs_1894_; uint8_t v_binaryProofs_1895_; uint8_t v_acNf_1896_; uint8_t v_andFlattening_1897_; uint8_t v_embeddedConstraintSubst_1898_; uint8_t v_fixedInt_1899_; uint8_t v_enums_1900_; uint8_t v_graphviz_1901_; lean_object* v_maxSteps_1902_; uint8_t v_shortCircuit_1903_; uint8_t v_solverMode_1904_; uint8_t v_uf_1905_; lean_object* v_cegarRounds_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1917_; 
v_timeout_1893_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_1894_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_1895_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_1896_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_1897_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1898_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_fixedInt_1899_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_1900_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_1901_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_1902_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_1903_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_1904_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_1905_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_1906_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1908_ = v_config_1696_;
v_isShared_1909_ = v_isSharedCheck_1917_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_cegarRounds_1906_);
lean_inc(v_maxSteps_1902_);
lean_inc(v_timeout_1893_);
lean_dec(v_config_1696_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1917_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_timeout_1893_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_maxSteps_1902_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_cegarRounds_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*3, v_trimProofs_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*3 + 1, v_binaryProofs_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*3 + 2, v_acNf_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*3 + 3, v_andFlattening_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1898_);
v___x_1911_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
uint8_t v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_unbox(v_a_1889_);
lean_dec(v_a_1889_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*3 + 5, v___x_1912_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*3 + 6, v_fixedInt_1899_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*3 + 7, v_enums_1900_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*3 + 8, v_graphviz_1901_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*3 + 9, v_shortCircuit_1903_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*3 + 10, v_solverMode_1904_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*3 + 11, v_uf_1905_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1911_);
v___x_1914_ = v___x_1891_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1911_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_config_1696_);
v_a_1919_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1888_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1888_);
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
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_1927_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1886_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1886_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
else
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_string_dec_eq(v___x_1712_, v___x_1714_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_1937_ = lean_string_dec_eq(v___x_1712_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10));
v___x_1939_ = lean_string_dec_eq(v___x_1712_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11));
v___x_1941_ = lean_string_dec_eq(v___x_1712_, v___x_1940_);
lean_dec_ref(v___x_1712_);
if (v___x_1941_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12));
v___x_1943_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_1942_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1943_) == 0)
{
uint8_t v___x_1944_; 
lean_dec_ref_known(v___x_1943_, 1);
v___x_1944_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_1944_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1945_; 
lean_dec_ref(v___x_1713_);
lean_inc_ref(v_item_1697_);
v___x_1945_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_value_1946_; lean_object* v___x_1947_; 
lean_dec_ref_known(v___x_1945_, 1);
v_value_1946_ = lean_ctor_get(v_item_1697_, 2);
lean_inc(v_value_1946_);
lean_dec_ref(v_item_1697_);
v___x_1947_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_value_1946_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1977_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1977_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1977_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_timeout_1952_; uint8_t v_trimProofs_1953_; uint8_t v_binaryProofs_1954_; uint8_t v_acNf_1955_; uint8_t v_andFlattening_1956_; uint8_t v_embeddedConstraintSubst_1957_; uint8_t v_structures_1958_; uint8_t v_fixedInt_1959_; uint8_t v_enums_1960_; uint8_t v_graphviz_1961_; lean_object* v_maxSteps_1962_; uint8_t v_shortCircuit_1963_; uint8_t v_uf_1964_; lean_object* v_cegarRounds_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1976_; 
v_timeout_1952_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_1953_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_1954_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_1955_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_1956_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1957_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_1958_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_1959_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_1960_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_1961_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_1962_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_1963_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_uf_1964_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_1965_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1967_ = v_config_1696_;
v_isShared_1968_ = v_isSharedCheck_1976_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_cegarRounds_1965_);
lean_inc(v_maxSteps_1962_);
lean_inc(v_timeout_1952_);
lean_dec(v_config_1696_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1976_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_timeout_1952_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_maxSteps_1962_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_cegarRounds_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3, v_trimProofs_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 1, v_binaryProofs_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 2, v_acNf_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 3, v_andFlattening_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 5, v_structures_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 6, v_fixedInt_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 7, v_enums_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 8, v_graphviz_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*3 + 9, v_shortCircuit_1963_);
v___x_1970_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
uint8_t v___x_1971_; lean_object* v___x_1973_; 
v___x_1971_ = lean_unbox(v_a_1948_);
lean_dec(v_a_1948_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*3 + 10, v___x_1971_);
lean_ctor_set_uint8(v___x_1970_, sizeof(void*)*3 + 11, v_uf_1964_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1970_);
v___x_1973_ = v___x_1950_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1970_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_config_1696_);
v_a_1978_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1947_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1947_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
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
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_1986_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1945_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1945_);
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
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_1994_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1943_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1943_);
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
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec_ref(v___x_1712_);
v___x_2002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13));
v___x_2003_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2002_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2003_) == 0)
{
uint8_t v___x_2004_; 
lean_dec_ref_known(v___x_2003_, 1);
v___x_2004_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2005_; 
lean_dec_ref(v___x_1713_);
v___x_2005_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2035_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2035_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2035_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_timeout_2010_; uint8_t v_trimProofs_2011_; uint8_t v_binaryProofs_2012_; uint8_t v_acNf_2013_; uint8_t v_andFlattening_2014_; uint8_t v_embeddedConstraintSubst_2015_; uint8_t v_structures_2016_; uint8_t v_fixedInt_2017_; uint8_t v_enums_2018_; uint8_t v_graphviz_2019_; lean_object* v_maxSteps_2020_; uint8_t v_solverMode_2021_; uint8_t v_uf_2022_; lean_object* v_cegarRounds_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2034_; 
v_timeout_2010_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2011_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2012_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2013_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2014_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2015_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2016_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2017_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2018_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2019_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2020_ = lean_ctor_get(v_config_1696_, 1);
v_solverMode_2021_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2022_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2023_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2025_ = v_config_1696_;
v_isShared_2026_ = v_isSharedCheck_2034_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_cegarRounds_2023_);
lean_inc(v_maxSteps_2020_);
lean_inc(v_timeout_2010_);
lean_dec(v_config_1696_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2034_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_timeout_2010_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_maxSteps_2020_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_cegarRounds_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3, v_trimProofs_2011_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 1, v_binaryProofs_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 2, v_acNf_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 3, v_andFlattening_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2015_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 5, v_structures_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 6, v_fixedInt_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 7, v_enums_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*3 + 8, v_graphviz_2019_);
v___x_2028_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
uint8_t v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_unbox(v_a_2006_);
lean_dec(v_a_2006_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*3 + 9, v___x_2029_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*3 + 10, v_solverMode_2021_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*3 + 11, v_uf_2022_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2028_);
v___x_2031_ = v___x_2008_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2028_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_config_1696_);
v_a_2036_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2005_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2005_);
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
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2044_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2003_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2003_);
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
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v___x_1712_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14));
v___x_2053_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2052_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2053_) == 0)
{
uint8_t v___x_2054_; 
lean_dec_ref_known(v___x_2053_, 1);
v___x_2054_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2054_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2055_; 
lean_dec_ref(v___x_1713_);
lean_inc_ref(v_item_1697_);
v___x_2055_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_value_2056_; lean_object* v___x_2057_; 
lean_dec_ref_known(v___x_2055_, 1);
v_value_2056_ = lean_ctor_get(v_item_1697_, 2);
lean_inc(v_value_2056_);
lean_dec_ref(v_item_1697_);
v___x_2057_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_2056_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2087_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2087_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2087_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_timeout_2062_; uint8_t v_trimProofs_2063_; uint8_t v_binaryProofs_2064_; uint8_t v_acNf_2065_; uint8_t v_andFlattening_2066_; uint8_t v_embeddedConstraintSubst_2067_; uint8_t v_structures_2068_; uint8_t v_fixedInt_2069_; uint8_t v_enums_2070_; uint8_t v_graphviz_2071_; uint8_t v_shortCircuit_2072_; uint8_t v_solverMode_2073_; uint8_t v_uf_2074_; lean_object* v_cegarRounds_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2085_; 
v_timeout_2062_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2063_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2064_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2065_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2066_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2067_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2068_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2069_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2070_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2071_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_shortCircuit_2072_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2073_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2074_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2075_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v_config_1696_, 1);
lean_dec(v_unused_2086_);
v___x_2077_ = v_config_1696_;
v_isShared_2078_ = v_isSharedCheck_2085_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_cegarRounds_2075_);
lean_inc(v_timeout_2062_);
lean_dec(v_config_1696_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2085_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v_a_2058_);
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_timeout_2062_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_a_2058_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_cegarRounds_2075_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3, v_trimProofs_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 1, v_binaryProofs_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 2, v_acNf_2065_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 3, v_andFlattening_2066_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2067_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 5, v_structures_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 6, v_fixedInt_2069_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 7, v_enums_2070_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 8, v_graphviz_2071_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 9, v_shortCircuit_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 10, v_solverMode_2073_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*3 + 11, v_uf_2074_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2082_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2080_);
v___x_2082_ = v___x_2060_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_config_1696_);
v_a_2088_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2057_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2057_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2096_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2055_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2055_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2104_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2053_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2053_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref(v___x_1712_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15));
v___x_2113_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2112_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2113_) == 0)
{
uint8_t v___x_2114_; 
lean_dec_ref_known(v___x_2113_, 1);
v___x_2114_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2114_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2115_; 
lean_dec_ref(v___x_1713_);
v___x_2115_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2145_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2145_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2145_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_timeout_2120_; uint8_t v_trimProofs_2121_; uint8_t v_binaryProofs_2122_; uint8_t v_acNf_2123_; uint8_t v_andFlattening_2124_; uint8_t v_embeddedConstraintSubst_2125_; uint8_t v_structures_2126_; uint8_t v_fixedInt_2127_; uint8_t v_enums_2128_; lean_object* v_maxSteps_2129_; uint8_t v_shortCircuit_2130_; uint8_t v_solverMode_2131_; uint8_t v_uf_2132_; lean_object* v_cegarRounds_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2144_; 
v_timeout_2120_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2121_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2122_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2123_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2124_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2125_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2126_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2127_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2128_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_maxSteps_2129_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2130_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2131_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2132_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2133_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2135_ = v_config_1696_;
v_isShared_2136_ = v_isSharedCheck_2144_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_cegarRounds_2133_);
lean_inc(v_maxSteps_2129_);
lean_inc(v_timeout_2120_);
lean_dec(v_config_1696_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2144_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_timeout_2120_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_maxSteps_2129_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_cegarRounds_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3, v_trimProofs_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3 + 1, v_binaryProofs_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3 + 2, v_acNf_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3 + 3, v_andFlattening_2124_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3 + 5, v_structures_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3 + 6, v_fixedInt_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*3 + 7, v_enums_2128_);
v___x_2138_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
uint8_t v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_unbox(v_a_2116_);
lean_dec(v_a_2116_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 8, v___x_2139_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 9, v_shortCircuit_2130_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 10, v_solverMode_2131_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*3 + 11, v_uf_2132_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2138_);
v___x_2141_ = v___x_2118_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2138_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v_config_1696_);
v_a_2146_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2115_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2115_);
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
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2154_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2113_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2113_);
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
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16));
v___x_2163_ = lean_string_dec_lt(v___x_1712_, v___x_2162_);
if (v___x_2163_ == 0)
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_string_dec_eq(v___x_1712_, v___x_2162_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17));
v___x_2166_ = lean_string_dec_eq(v___x_1712_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18));
v___x_2168_ = lean_string_dec_eq(v___x_1712_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19));
v___x_2170_ = lean_string_dec_eq(v___x_1712_, v___x_2169_);
lean_dec_ref(v___x_1712_);
if (v___x_2170_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20));
v___x_2172_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2171_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2172_) == 0)
{
uint8_t v___x_2173_; 
lean_dec_ref_known(v___x_2172_, 1);
v___x_2173_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2173_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2174_; 
lean_dec_ref(v___x_1713_);
v___x_2174_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2204_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2204_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2204_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_timeout_2179_; uint8_t v_trimProofs_2180_; uint8_t v_binaryProofs_2181_; uint8_t v_acNf_2182_; uint8_t v_andFlattening_2183_; uint8_t v_embeddedConstraintSubst_2184_; uint8_t v_structures_2185_; uint8_t v_enums_2186_; uint8_t v_graphviz_2187_; lean_object* v_maxSteps_2188_; uint8_t v_shortCircuit_2189_; uint8_t v_solverMode_2190_; uint8_t v_uf_2191_; lean_object* v_cegarRounds_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2203_; 
v_timeout_2179_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2180_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2181_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2182_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2183_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2184_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2185_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_enums_2186_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2187_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2188_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2189_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2190_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2191_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2192_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2194_ = v_config_1696_;
v_isShared_2195_ = v_isSharedCheck_2203_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_cegarRounds_2192_);
lean_inc(v_maxSteps_2188_);
lean_inc(v_timeout_2179_);
lean_dec(v_config_1696_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2203_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_timeout_2179_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_maxSteps_2188_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_cegarRounds_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*3, v_trimProofs_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*3 + 1, v_binaryProofs_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*3 + 2, v_acNf_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*3 + 3, v_andFlattening_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2202_, sizeof(void*)*3 + 5, v_structures_2185_);
v___x_2197_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
uint8_t v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_unbox(v_a_2175_);
lean_dec(v_a_2175_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 6, v___x_2198_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 7, v_enums_2186_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 8, v_graphviz_2187_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 9, v_shortCircuit_2189_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 10, v_solverMode_2190_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 11, v_uf_2191_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2197_);
v___x_2200_ = v___x_2177_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2197_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v_config_1696_);
v_a_2205_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2174_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2174_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2213_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2172_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2172_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
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
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v___x_1712_);
v___x_2221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21));
v___x_2222_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2221_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2222_) == 0)
{
uint8_t v___x_2223_; 
lean_dec_ref_known(v___x_2222_, 1);
v___x_2223_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2223_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2224_; 
lean_dec_ref(v___x_1713_);
v___x_2224_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2254_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2254_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2254_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_timeout_2229_; uint8_t v_trimProofs_2230_; uint8_t v_binaryProofs_2231_; uint8_t v_acNf_2232_; uint8_t v_andFlattening_2233_; uint8_t v_embeddedConstraintSubst_2234_; uint8_t v_structures_2235_; uint8_t v_fixedInt_2236_; uint8_t v_graphviz_2237_; lean_object* v_maxSteps_2238_; uint8_t v_shortCircuit_2239_; uint8_t v_solverMode_2240_; uint8_t v_uf_2241_; lean_object* v_cegarRounds_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2253_; 
v_timeout_2229_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2230_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2231_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2232_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2233_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2234_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2235_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2236_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_graphviz_2237_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2238_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2239_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2240_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2241_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2242_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2244_ = v_config_1696_;
v_isShared_2245_ = v_isSharedCheck_2253_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_cegarRounds_2242_);
lean_inc(v_maxSteps_2238_);
lean_inc(v_timeout_2229_);
lean_dec(v_config_1696_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2253_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_timeout_2229_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_maxSteps_2238_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_cegarRounds_2242_);
lean_ctor_set_uint8(v_reuseFailAlloc_2252_, sizeof(void*)*3, v_trimProofs_2230_);
lean_ctor_set_uint8(v_reuseFailAlloc_2252_, sizeof(void*)*3 + 1, v_binaryProofs_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2252_, sizeof(void*)*3 + 2, v_acNf_2232_);
lean_ctor_set_uint8(v_reuseFailAlloc_2252_, sizeof(void*)*3 + 3, v_andFlattening_2233_);
lean_ctor_set_uint8(v_reuseFailAlloc_2252_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2234_);
lean_ctor_set_uint8(v_reuseFailAlloc_2252_, sizeof(void*)*3 + 5, v_structures_2235_);
lean_ctor_set_uint8(v_reuseFailAlloc_2252_, sizeof(void*)*3 + 6, v_fixedInt_2236_);
v___x_2247_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
uint8_t v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = lean_unbox(v_a_2225_);
lean_dec(v_a_2225_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 7, v___x_2248_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 8, v_graphviz_2237_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 9, v_shortCircuit_2239_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 10, v_solverMode_2240_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 11, v_uf_2241_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2247_);
v___x_2250_ = v___x_2227_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2247_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec_ref(v_config_1696_);
v_a_2255_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2224_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2224_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2263_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2222_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2222_);
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
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v___x_1712_);
v___x_2271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22));
v___x_2272_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2271_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2272_) == 0)
{
uint8_t v___x_2273_; 
lean_dec_ref_known(v___x_2272_, 1);
v___x_2273_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2273_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2274_; 
lean_dec_ref(v___x_1713_);
v___x_2274_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2304_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2304_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2304_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v_timeout_2279_; uint8_t v_trimProofs_2280_; uint8_t v_binaryProofs_2281_; uint8_t v_acNf_2282_; uint8_t v_andFlattening_2283_; uint8_t v_structures_2284_; uint8_t v_fixedInt_2285_; uint8_t v_enums_2286_; uint8_t v_graphviz_2287_; lean_object* v_maxSteps_2288_; uint8_t v_shortCircuit_2289_; uint8_t v_solverMode_2290_; uint8_t v_uf_2291_; lean_object* v_cegarRounds_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2303_; 
v_timeout_2279_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2280_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2281_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2282_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2283_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_structures_2284_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2285_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2286_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2287_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2288_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2289_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2290_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2291_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2292_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2294_ = v_config_1696_;
v_isShared_2295_ = v_isSharedCheck_2303_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_cegarRounds_2292_);
lean_inc(v_maxSteps_2288_);
lean_inc(v_timeout_2279_);
lean_dec(v_config_1696_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2303_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_timeout_2279_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_maxSteps_2288_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_cegarRounds_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2302_, sizeof(void*)*3, v_trimProofs_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2302_, sizeof(void*)*3 + 1, v_binaryProofs_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2302_, sizeof(void*)*3 + 2, v_acNf_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2302_, sizeof(void*)*3 + 3, v_andFlattening_2283_);
v___x_2297_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
uint8_t v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_unbox(v_a_2275_);
lean_dec(v_a_2275_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 4, v___x_2298_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 5, v_structures_2284_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 6, v_fixedInt_2285_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 7, v_enums_2286_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 8, v_graphviz_2287_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 9, v_shortCircuit_2289_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 10, v_solverMode_2290_);
lean_ctor_set_uint8(v___x_2297_, sizeof(void*)*3 + 11, v_uf_2291_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2297_);
v___x_2300_ = v___x_2277_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2297_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_config_1696_);
v_a_2305_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2274_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2274_);
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
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2313_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2272_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2272_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
else
{
uint8_t v___x_2321_; 
lean_dec_ref(v___x_1712_);
lean_dec_ref(v_config_1696_);
v___x_2321_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2321_ == 0)
{
lean_dec_ref(v_item_1697_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v_value_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v___x_1713_);
v_value_2322_ = lean_ctor_get(v_item_1697_, 2);
lean_inc(v_value_2322_);
lean_dec_ref(v_item_1697_);
v___x_2323_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_value_2322_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_2323_;
}
}
}
else
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23));
v___x_2325_ = lean_string_dec_eq(v___x_1712_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24));
v___x_2327_ = lean_string_dec_eq(v___x_1712_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25));
v___x_2329_ = lean_string_dec_eq(v___x_1712_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26));
v___x_2331_ = lean_string_dec_eq(v___x_1712_, v___x_2330_);
lean_dec_ref(v___x_1712_);
if (v___x_2331_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27));
v___x_2333_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2332_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2333_) == 0)
{
uint8_t v___x_2334_; 
lean_dec_ref_known(v___x_2333_, 1);
v___x_2334_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2335_; 
lean_dec_ref(v___x_1713_);
lean_inc_ref(v_item_1697_);
v___x_2335_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_value_2336_; lean_object* v___x_2337_; 
lean_dec_ref_known(v___x_2335_, 1);
v_value_2336_ = lean_ctor_get(v_item_1697_, 2);
lean_inc(v_value_2336_);
lean_dec_ref(v_item_1697_);
v___x_2337_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_2336_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2367_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2367_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2367_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v_timeout_2342_; uint8_t v_trimProofs_2343_; uint8_t v_binaryProofs_2344_; uint8_t v_acNf_2345_; uint8_t v_andFlattening_2346_; uint8_t v_embeddedConstraintSubst_2347_; uint8_t v_structures_2348_; uint8_t v_fixedInt_2349_; uint8_t v_enums_2350_; uint8_t v_graphviz_2351_; lean_object* v_maxSteps_2352_; uint8_t v_shortCircuit_2353_; uint8_t v_solverMode_2354_; uint8_t v_uf_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2365_; 
v_timeout_2342_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2343_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2344_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2345_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2346_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2347_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2348_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2349_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2350_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2351_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2352_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2353_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2354_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2355_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v_config_1696_, 2);
lean_dec(v_unused_2366_);
v___x_2357_ = v_config_1696_;
v_isShared_2358_ = v_isSharedCheck_2365_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_maxSteps_2352_);
lean_inc(v_timeout_2342_);
lean_dec(v_config_1696_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2365_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 2, v_a_2338_);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_timeout_2342_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_maxSteps_2352_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_a_2338_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3, v_trimProofs_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 1, v_binaryProofs_2344_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 2, v_acNf_2345_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 3, v_andFlattening_2346_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2347_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 5, v_structures_2348_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 6, v_fixedInt_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 7, v_enums_2350_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 8, v_graphviz_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 9, v_shortCircuit_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 10, v_solverMode_2354_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*3 + 11, v_uf_2355_);
v___x_2360_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2362_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2360_);
v___x_2362_ = v___x_2340_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v_config_1696_);
v_a_2368_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2337_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2337_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2376_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2335_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2335_);
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
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2384_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2333_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2333_);
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
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_dec_ref(v___x_1712_);
v___x_2392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28));
v___x_2393_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2392_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2393_) == 0)
{
uint8_t v___x_2394_; 
lean_dec_ref_known(v___x_2393_, 1);
v___x_2394_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2394_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2395_; 
lean_dec_ref(v___x_1713_);
v___x_2395_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2425_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2425_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2425_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_timeout_2400_; uint8_t v_trimProofs_2401_; uint8_t v_acNf_2402_; uint8_t v_andFlattening_2403_; uint8_t v_embeddedConstraintSubst_2404_; uint8_t v_structures_2405_; uint8_t v_fixedInt_2406_; uint8_t v_enums_2407_; uint8_t v_graphviz_2408_; lean_object* v_maxSteps_2409_; uint8_t v_shortCircuit_2410_; uint8_t v_solverMode_2411_; uint8_t v_uf_2412_; lean_object* v_cegarRounds_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2424_; 
v_timeout_2400_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2401_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_acNf_2402_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_andFlattening_2403_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2404_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2405_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2406_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2407_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2408_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2409_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2410_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2411_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2412_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2413_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2415_ = v_config_1696_;
v_isShared_2416_ = v_isSharedCheck_2424_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_cegarRounds_2413_);
lean_inc(v_maxSteps_2409_);
lean_inc(v_timeout_2400_);
lean_dec(v_config_1696_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2424_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_timeout_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_maxSteps_2409_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v_cegarRounds_2413_);
lean_ctor_set_uint8(v_reuseFailAlloc_2423_, sizeof(void*)*3, v_trimProofs_2401_);
v___x_2418_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
uint8_t v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_unbox(v_a_2396_);
lean_dec(v_a_2396_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 1, v___x_2419_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 2, v_acNf_2402_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 3, v_andFlattening_2403_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2404_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 5, v_structures_2405_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 6, v_fixedInt_2406_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 7, v_enums_2407_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 8, v_graphviz_2408_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 9, v_shortCircuit_2410_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 10, v_solverMode_2411_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*3 + 11, v_uf_2412_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2418_);
v___x_2421_ = v___x_2398_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2418_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v_config_1696_);
v_a_2426_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2395_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2395_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2434_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2393_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2393_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec_ref(v___x_1712_);
v___x_2442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29));
v___x_2443_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2442_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2443_) == 0)
{
uint8_t v___x_2444_; 
lean_dec_ref_known(v___x_2443_, 1);
v___x_2444_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2444_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2445_; 
lean_dec_ref(v___x_1713_);
v___x_2445_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2475_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2475_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2475_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v_timeout_2450_; uint8_t v_trimProofs_2451_; uint8_t v_binaryProofs_2452_; uint8_t v_acNf_2453_; uint8_t v_embeddedConstraintSubst_2454_; uint8_t v_structures_2455_; uint8_t v_fixedInt_2456_; uint8_t v_enums_2457_; uint8_t v_graphviz_2458_; lean_object* v_maxSteps_2459_; uint8_t v_shortCircuit_2460_; uint8_t v_solverMode_2461_; uint8_t v_uf_2462_; lean_object* v_cegarRounds_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2474_; 
v_timeout_2450_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2451_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2452_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_acNf_2453_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 2);
v_embeddedConstraintSubst_2454_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2455_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2456_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2457_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2458_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2459_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2460_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2461_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2462_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2463_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2465_ = v_config_1696_;
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_cegarRounds_2463_);
lean_inc(v_maxSteps_2459_);
lean_inc(v_timeout_2450_);
lean_dec(v_config_1696_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_timeout_2450_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_maxSteps_2459_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_cegarRounds_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2473_, sizeof(void*)*3, v_trimProofs_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2473_, sizeof(void*)*3 + 1, v_binaryProofs_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2473_, sizeof(void*)*3 + 2, v_acNf_2453_);
v___x_2468_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
uint8_t v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_unbox(v_a_2446_);
lean_dec(v_a_2446_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 3, v___x_2469_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2454_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 5, v_structures_2455_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 6, v_fixedInt_2456_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 7, v_enums_2457_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 8, v_graphviz_2458_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 9, v_shortCircuit_2460_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 10, v_solverMode_2461_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 11, v_uf_2462_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2468_);
v___x_2471_ = v___x_2448_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2468_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_config_1696_);
v_a_2476_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2445_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2445_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2484_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2443_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2443_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec_ref(v___x_1712_);
v___x_2492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30));
v___x_2493_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1697_, v___x_2492_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2493_) == 0)
{
uint8_t v___x_2494_; 
lean_dec_ref_known(v___x_2493_, 1);
v___x_2494_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1713_);
if (v___x_2494_ == 0)
{
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_item_1706_ = v___x_1713_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_2495_; 
lean_dec_ref(v___x_1713_);
v___x_2495_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2525_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2525_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2525_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_timeout_2500_; uint8_t v_trimProofs_2501_; uint8_t v_binaryProofs_2502_; uint8_t v_andFlattening_2503_; uint8_t v_embeddedConstraintSubst_2504_; uint8_t v_structures_2505_; uint8_t v_fixedInt_2506_; uint8_t v_enums_2507_; uint8_t v_graphviz_2508_; lean_object* v_maxSteps_2509_; uint8_t v_shortCircuit_2510_; uint8_t v_solverMode_2511_; uint8_t v_uf_2512_; lean_object* v_cegarRounds_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2524_; 
v_timeout_2500_ = lean_ctor_get(v_config_1696_, 0);
v_trimProofs_2501_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3);
v_binaryProofs_2502_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 1);
v_andFlattening_2503_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2504_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 4);
v_structures_2505_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 5);
v_fixedInt_2506_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 6);
v_enums_2507_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 7);
v_graphviz_2508_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 8);
v_maxSteps_2509_ = lean_ctor_get(v_config_1696_, 1);
v_shortCircuit_2510_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 9);
v_solverMode_2511_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 10);
v_uf_2512_ = lean_ctor_get_uint8(v_config_1696_, sizeof(void*)*3 + 11);
v_cegarRounds_2513_ = lean_ctor_get(v_config_1696_, 2);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_config_1696_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2515_ = v_config_1696_;
v_isShared_2516_ = v_isSharedCheck_2524_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_cegarRounds_2513_);
lean_inc(v_maxSteps_2509_);
lean_inc(v_timeout_2500_);
lean_dec(v_config_1696_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2524_;
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
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_timeout_2500_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_maxSteps_2509_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_cegarRounds_2513_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*3, v_trimProofs_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2523_, sizeof(void*)*3 + 1, v_binaryProofs_2502_);
v___x_2518_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
uint8_t v___x_2519_; lean_object* v___x_2521_; 
v___x_2519_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 2, v___x_2519_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 3, v_andFlattening_2503_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2504_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 5, v_structures_2505_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 6, v_fixedInt_2506_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 7, v_enums_2507_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 8, v_graphviz_2508_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 9, v_shortCircuit_2510_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 10, v_solverMode_2511_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 11, v_uf_2512_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2518_);
v___x_2521_ = v___x_2498_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2518_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_config_1696_);
v_a_2526_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2495_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2495_);
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
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2534_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2493_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2493_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_config_1696_);
v_item_1706_ = v_item_1697_;
goto v___jp_1705_;
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v_item_1697_);
lean_dec_ref(v_config_1696_);
v_a_2542_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_1710_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_1710_);
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
v___jp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_1708_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1706_, v___x_1707_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_2550_, lean_object* v_item_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(v_config_2550_, v_item_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object* v_e_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_2562_, v___y_2566_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_e_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(v_e_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object* v_00_u03b1_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(v_00_u03b1_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object* v_00_u03b1_2598_, lean_object* v_msg_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_msg_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(v_00_u03b1_2608_, v_msg_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object* v_msgData_2618_, lean_object* v_macroStack_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_2618_, v_macroStack_2619_, v___y_2624_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object* v_msgData_2628_, lean_object* v_macroStack_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(v_msgData_2628_, v_macroStack_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
return v_res_2637_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_box(0);
v___x_2639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_2640_ = l_Lean_mkConst(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0);
v___x_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(lean_object* v_cfg_2643_, lean_object* v_cfgItem_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1);
v___x_2653_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2643_, v_cfgItem_2644_, v___x_2652_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_2654_, lean_object* v_cfgItem_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(v_cfg_2654_, v_cfgItem_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v_cfgItem_2655_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object* v_cfg_2665_, lean_object* v_init_2666_, uint8_t v_logExceptions_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_onErr_2672_; lean_object* v_eval_2673_; 
v_onErr_2672_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0));
v_eval_2673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_2667_ == 0)
{
lean_object* v___x_2674_; 
v___x_2674_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2673_, v_init_2666_, v_cfg_2665_, v_onErr_2672_, v_logExceptions_2667_, v_a_2669_, v_a_2670_);
return v___x_2674_;
}
else
{
uint8_t v_recover_2675_; lean_object* v___x_2676_; 
v_recover_2675_ = lean_ctor_get_uint8(v_a_2668_, sizeof(void*)*1);
v___x_2676_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2673_, v_init_2666_, v_cfg_2665_, v_onErr_2672_, v_recover_2675_, v_a_2669_, v_a_2670_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_2677_, lean_object* v_init_2678_, lean_object* v_logExceptions_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_logExceptions_boxed_2684_; lean_object* v_res_2685_; 
v_logExceptions_boxed_2684_ = lean_unbox(v_logExceptions_2679_);
v_res_2685_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2677_, v_init_2678_, v_logExceptions_boxed_2684_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(lean_object* v_cfg_2686_, lean_object* v_init_2687_, uint8_t v_logExceptions_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2686_, v_init_2687_, v_logExceptions_2688_, v_a_2689_, v_a_2695_, v_a_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___boxed(lean_object* v_cfg_2699_, lean_object* v_init_2700_, lean_object* v_logExceptions_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
uint8_t v_logExceptions_boxed_2711_; lean_object* v_res_2712_; 
v_logExceptions_boxed_2711_ = lean_unbox(v_logExceptions_2701_);
v_res_2712_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(v_cfg_2699_, v_init_2700_, v_logExceptions_boxed_2711_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
return v_res_2712_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2713_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
lean_ctor_set(v___x_2718_, 3, v___x_2717_);
lean_ctor_set(v___x_2718_, 4, v___x_2716_);
lean_ctor_set(v___x_2718_, 5, v___x_2716_);
lean_ctor_set(v___x_2718_, 6, v___x_2716_);
lean_ctor_set(v___x_2718_, 7, v___x_2716_);
lean_ctor_set(v___x_2718_, 8, v___x_2716_);
lean_ctor_set(v___x_2718_, 9, v___x_2716_);
lean_ctor_set(v___x_2718_, 10, v___x_2716_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_unsigned_to_nat(32u);
v___x_2720_ = lean_mk_empty_array_with_capacity(v___x_2719_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2722_ = ((size_t)5ULL);
v___x_2723_ = lean_unsigned_to_nat(0u);
v___x_2724_ = lean_unsigned_to_nat(32u);
v___x_2725_ = lean_mk_empty_array_with_capacity(v___x_2724_);
v___x_2726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3);
v___x_2727_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v___x_2725_);
lean_ctor_set(v___x_2727_, 2, v___x_2723_);
lean_ctor_set(v___x_2727_, 3, v___x_2723_);
lean_ctor_set_usize(v___x_2727_, 4, v___x_2722_);
return v___x_2727_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2728_ = lean_box(1);
v___x_2729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4);
v___x_2730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
lean_ctor_set(v___x_2731_, 1, v___x_2729_);
lean_ctor_set(v___x_2731_, 2, v___x_2728_);
return v___x_2731_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__6));
v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
return v___x_2734_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__8));
v___x_2737_ = l_Lean_stringToMessageData(v___x_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__10));
v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
return v___x_2740_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__12));
v___x_2743_ = l_Lean_stringToMessageData(v___x_2742_);
return v___x_2743_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__14));
v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16));
v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_msg_2753_, lean_object* v_declHint_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v_env_2759_; uint8_t v___x_2760_; 
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_st_ref_get(v___y_2755_);
v_env_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc_ref(v_env_2759_);
lean_dec(v___x_2758_);
v___x_2760_ = l_Lean_Name_isAnonymous(v_declHint_2754_);
if (v___x_2760_ == 0)
{
uint8_t v_isExporting_2761_; 
v_isExporting_2761_ = lean_ctor_get_uint8(v_env_2759_, sizeof(void*)*8);
if (v_isExporting_2761_ == 0)
{
lean_object* v___x_2762_; 
lean_dec_ref(v_env_2759_);
lean_dec(v_declHint_2754_);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v_msg_2753_);
return v___x_2762_;
}
else
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
lean_inc_ref(v_env_2759_);
v___x_2763_ = l_Lean_Environment_setExporting(v_env_2759_, v___x_2760_);
lean_inc(v_declHint_2754_);
lean_inc_ref(v___x_2763_);
v___x_2764_ = l_Lean_Environment_contains(v___x_2763_, v_declHint_2754_, v_isExporting_2761_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
lean_dec_ref(v___x_2763_);
lean_dec_ref(v_env_2759_);
lean_dec(v_declHint_2754_);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_msg_2753_);
return v___x_2765_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v_c_2771_; lean_object* v___x_2772_; 
v___x_2766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
v___x_2768_ = l_Lean_Options_empty;
v___x_2769_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2763_);
lean_ctor_set(v___x_2769_, 1, v___x_2766_);
lean_ctor_set(v___x_2769_, 2, v___x_2767_);
lean_ctor_set(v___x_2769_, 3, v___x_2768_);
lean_inc(v_declHint_2754_);
v___x_2770_ = l_Lean_MessageData_ofConstName(v_declHint_2754_, v___x_2760_);
v_c_2771_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2771_, 0, v___x_2769_);
lean_ctor_set(v_c_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2759_, v_declHint_2754_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec_ref(v_env_2759_);
lean_dec(v_declHint_2754_);
v___x_2773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v_c_2771_);
v___x_2775_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9);
v___x_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = l_Lean_MessageData_note(v___x_2776_);
v___x_2778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_msg_2753_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
return v___x_2779_;
}
else
{
lean_object* v_val_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2814_; 
v_val_2780_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2782_ = v___x_2772_;
v_isShared_2783_ = v_isSharedCheck_2814_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_val_2780_);
lean_dec(v___x_2772_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2814_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_mod_2786_; uint8_t v___x_2787_; 
v___x_2784_ = l_Lean_Environment_header(v_env_2759_);
lean_dec_ref(v_env_2759_);
v___x_2785_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2784_);
v_mod_2786_ = lean_array_get(v___x_2757_, v___x_2785_, v_val_2780_);
lean_dec(v_val_2780_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = l_Lean_isPrivateName(v_declHint_2754_);
lean_dec(v_declHint_2754_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v_c_2771_);
v___x_2790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l_Lean_MessageData_ofName(v_mod_2786_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_MessageData_note(v___x_2795_);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_msg_2753_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2797_);
v___x_2799_ = v___x_2782_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2801_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v_c_2771_);
v___x_2803_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = l_Lean_MessageData_ofName(v_mod_2786_);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_MessageData_note(v___x_2808_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v_msg_2753_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2810_);
v___x_2812_ = v___x_2782_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2815_; 
lean_dec_ref(v_env_2759_);
lean_dec(v_declHint_2754_);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v_msg_2753_);
return v___x_2815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2816_, lean_object* v_declHint_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2816_, v_declHint_2817_, v___y_2818_);
lean_dec(v___y_2818_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_msg_2821_, lean_object* v_declHint_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2836_; 
v___x_2826_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2821_, v_declHint_2822_, v___y_2824_);
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2836_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2836_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2831_ = l_Lean_unknownIdentifierMessageTag;
v___x_2832_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v_a_2827_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2832_);
v___x_2834_ = v___x_2829_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_msg_2837_, lean_object* v_declHint_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2837_, v_declHint_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(lean_object* v_msgData_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; lean_object* v_toCold_2848_; lean_object* v_env_2849_; lean_object* v_options_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2847_ = lean_st_ref_get(v___y_2845_);
v_toCold_2848_ = lean_ctor_get(v___y_2844_, 0);
v_env_2849_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_ref(v_env_2849_);
lean_dec(v___x_2847_);
v_options_2850_ = lean_ctor_get(v_toCold_2848_, 2);
v___x_2851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2852_ = lean_unsigned_to_nat(32u);
v___x_2853_ = lean_mk_empty_array_with_capacity(v___x_2852_);
lean_dec_ref(v___x_2853_);
v___x_2854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2850_);
v___x_2855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2855_, 0, v_env_2849_);
lean_ctor_set(v___x_2855_, 1, v___x_2851_);
lean_ctor_set(v___x_2855_, 2, v___x_2854_);
lean_ctor_set(v___x_2855_, 3, v_options_2850_);
v___x_2856_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v_msgData_2843_);
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msgData_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_msg_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_ref_2867_; lean_object* v___x_2868_; lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2877_; 
v_ref_2867_ = lean_ctor_get(v___y_2864_, 2);
v___x_2868_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msg_2863_, v___y_2864_, v___y_2865_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2877_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2877_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2875_; 
lean_inc(v_ref_2867_);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v_ref_2867_);
lean_ctor_set(v___x_2873_, 1, v_a_2869_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set_tag(v___x_2871_, 1);
lean_ctor_set(v___x_2871_, 0, v___x_2873_);
v___x_2875_ = v___x_2871_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_msg_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_ref_2883_, lean_object* v_msg_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_toCold_2888_; lean_object* v_currRecDepth_2889_; lean_object* v_ref_2890_; uint16_t v_optionFlags_2891_; uint8_t v_suppressElabErrors_2892_; uint8_t v_isRecordingDeps_2893_; lean_object* v_ref_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_toCold_2888_ = lean_ctor_get(v___y_2885_, 0);
v_currRecDepth_2889_ = lean_ctor_get(v___y_2885_, 1);
v_ref_2890_ = lean_ctor_get(v___y_2885_, 2);
v_optionFlags_2891_ = lean_ctor_get_uint16(v___y_2885_, sizeof(void*)*3);
v_suppressElabErrors_2892_ = lean_ctor_get_uint8(v___y_2885_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2893_ = lean_ctor_get_uint8(v___y_2885_, sizeof(void*)*3 + 3);
v_ref_2894_ = l_Lean_replaceRef(v_ref_2883_, v_ref_2890_);
lean_inc(v_currRecDepth_2889_);
lean_inc_ref(v_toCold_2888_);
v___x_2895_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2895_, 0, v_toCold_2888_);
lean_ctor_set(v___x_2895_, 1, v_currRecDepth_2889_);
lean_ctor_set(v___x_2895_, 2, v_ref_2894_);
lean_ctor_set_uint16(v___x_2895_, sizeof(void*)*3, v_optionFlags_2891_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*3 + 2, v_suppressElabErrors_2892_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*3 + 3, v_isRecordingDeps_2893_);
v___x_2896_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2884_, v___x_2895_, v___y_2886_);
lean_dec_ref_known(v___x_2895_, 3);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_ref_2897_, lean_object* v_msg_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2897_, v_msg_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v_ref_2897_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2903_, lean_object* v_msg_2904_, lean_object* v_declHint_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; lean_object* v_a_2910_; lean_object* v___x_2911_; 
v___x_2909_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2904_, v_declHint_2905_, v___y_2906_, v___y_2907_);
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___x_2909_);
v___x_2911_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2903_, v_a_2910_, v___y_2906_, v___y_2907_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2912_, lean_object* v_msg_2913_, lean_object* v_declHint_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2912_, v_msg_2913_, v_declHint_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v_ref_2912_);
return v_res_2918_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2921_ = l_Lean_stringToMessageData(v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2922_, lean_object* v_constName_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2927_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2928_ = 0;
lean_inc(v_constName_2923_);
v___x_2929_ = l_Lean_MessageData_ofConstName(v_constName_2923_, v___x_2928_);
v___x_2930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2927_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_2932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2922_, v___x_2932_, v_constName_2923_, v___y_2924_, v___y_2925_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2934_, lean_object* v_constName_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_2934_, v_constName_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v_ref_2934_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(lean_object* v_constName_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_ref_2944_; lean_object* v___x_2945_; 
v_ref_2944_ = lean_ctor_get(v___y_2941_, 2);
v___x_2945_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_2944_, v_constName_2940_, v___y_2941_, v___y_2942_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(lean_object* v_constName_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; lean_object* v_env_2956_; uint8_t v___x_2957_; lean_object* v___x_2958_; 
v___x_2955_ = lean_st_ref_get(v___y_2953_);
v_env_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc_ref(v_env_2956_);
lean_dec(v___x_2955_);
v___x_2957_ = 0;
lean_inc(v_constName_2951_);
v___x_2958_ = l_Lean_Environment_find_x3f(v_env_2956_, v_constName_2951_, v___x_2957_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_2951_, v___y_2952_, v___y_2953_);
return v___x_2959_;
}
else
{
lean_object* v_val_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v_constName_2951_);
v_val_2960_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2958_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_val_2960_);
lean_dec(v___x_2958_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 0);
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_val_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0___boxed(lean_object* v_constName_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_constName_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(uint8_t v___x_2973_, lean_object* v_x_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
if (lean_obj_tag(v_x_2974_) == 0)
{
uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = 1;
v___x_2979_ = lean_box(v___x_2978_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
else
{
lean_object* v_head_2981_; lean_object* v_tail_2982_; lean_object* v___y_2984_; uint8_t v_a_2985_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_head_2981_ = lean_ctor_get(v_x_2974_, 0);
lean_inc(v_head_2981_);
v_tail_2982_ = lean_ctor_get(v_x_2974_, 1);
lean_inc(v_tail_2982_);
lean_dec_ref_known(v_x_2974_, 2);
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_head_2981_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3004_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_3004_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3004_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
if (lean_obj_tag(v_a_2989_) == 6)
{
lean_object* v_val_2993_; lean_object* v_numFields_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
v_val_2993_ = lean_ctor_get(v_a_2989_, 0);
lean_inc_ref(v_val_2993_);
lean_dec_ref_known(v_a_2989_, 1);
v_numFields_2994_ = lean_ctor_get(v_val_2993_, 4);
lean_inc(v_numFields_2994_);
lean_dec_ref(v_val_2993_);
v___x_2995_ = lean_nat_dec_eq(v_numFields_2994_, v___x_2987_);
lean_dec(v_numFields_2994_);
v___x_2996_ = lean_box(v___x_2995_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2996_);
v___x_2998_ = v___x_2991_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
v___y_2984_ = v___x_2998_;
v_a_2985_ = v___x_2995_;
goto v___jp_2983_;
}
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3002_; 
lean_dec(v_a_2989_);
v___x_3000_ = lean_box(v___x_2973_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_3000_);
v___x_3002_ = v___x_2991_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
v___y_2984_ = v___x_3002_;
v_a_2985_ = v___x_2973_;
goto v___jp_2983_;
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_tail_2982_);
v_a_3005_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2988_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2988_);
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
v___jp_2983_:
{
if (v_a_2985_ == 0)
{
lean_dec(v_tail_2982_);
return v___y_2984_;
}
else
{
lean_dec_ref(v___y_2984_);
v_x_2974_ = v_tail_2982_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2___boxed(lean_object* v___x_3013_, lean_object* v_x_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
uint8_t v___x_4236__boxed_3018_; lean_object* v_res_3019_; 
v___x_4236__boxed_3018_ = lean_unbox(v___x_3013_);
v_res_3019_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v___x_4236__boxed_3018_, v_x_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(lean_object* v_declName_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_3020_, v___y_3021_, v___y_3022_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3080_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3080_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3080_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
if (lean_obj_tag(v_a_3025_) == 5)
{
lean_object* v_val_3029_; lean_object* v_toConstantVal_3030_; lean_object* v_numParams_3031_; lean_object* v_numIndices_3032_; lean_object* v_ctors_3033_; uint8_t v_isRec_3034_; uint8_t v_isUnsafe_3035_; lean_object* v_type_3036_; uint8_t v___x_3037_; 
v_val_3029_ = lean_ctor_get(v_a_3025_, 0);
lean_inc_ref(v_val_3029_);
lean_dec_ref_known(v_a_3025_, 1);
v_toConstantVal_3030_ = lean_ctor_get(v_val_3029_, 0);
v_numParams_3031_ = lean_ctor_get(v_val_3029_, 1);
lean_inc(v_numParams_3031_);
v_numIndices_3032_ = lean_ctor_get(v_val_3029_, 2);
lean_inc(v_numIndices_3032_);
v_ctors_3033_ = lean_ctor_get(v_val_3029_, 4);
lean_inc(v_ctors_3033_);
v_isRec_3034_ = lean_ctor_get_uint8(v_val_3029_, sizeof(void*)*6);
v_isUnsafe_3035_ = lean_ctor_get_uint8(v_val_3029_, sizeof(void*)*6 + 1);
v_type_3036_ = lean_ctor_get(v_toConstantVal_3030_, 2);
v___x_3037_ = l_Lean_Expr_isProp(v_type_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3038_ = l_Lean_InductiveVal_numTypeFormers(v_val_3029_);
lean_dec_ref(v_val_3029_);
v___x_3039_ = lean_unsigned_to_nat(1u);
v___x_3040_ = lean_nat_dec_eq(v___x_3038_, v___x_3039_);
lean_dec(v___x_3038_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
lean_dec(v_ctors_3033_);
lean_dec(v_numIndices_3032_);
lean_dec(v_numParams_3031_);
v___x_3041_ = lean_box(v___x_3040_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3041_);
v___x_3043_ = v___x_3027_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = lean_nat_dec_eq(v_numIndices_3032_, v___x_3045_);
lean_dec(v_numIndices_3032_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
lean_dec(v_ctors_3033_);
lean_dec(v_numParams_3031_);
v___x_3047_ = lean_box(v___x_3046_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3047_);
v___x_3049_ = v___x_3027_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
else
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_nat_dec_eq(v_numParams_3031_, v___x_3045_);
lean_dec(v_numParams_3031_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
lean_dec(v_ctors_3033_);
v___x_3052_ = lean_box(v___x_3051_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3052_);
v___x_3054_ = v___x_3027_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = l_List_isEmpty___redArg(v_ctors_3033_);
if (v___x_3056_ == 0)
{
if (v_isRec_3034_ == 0)
{
if (v_isUnsafe_3035_ == 0)
{
lean_object* v___x_3057_; 
lean_del_object(v___x_3027_);
v___x_3057_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v_isUnsafe_3035_, v_ctors_3033_, v___y_3021_, v___y_3022_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
lean_dec(v_ctors_3033_);
v___x_3058_ = lean_box(v_isRec_3034_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3058_);
v___x_3060_ = v___x_3027_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
lean_dec(v_ctors_3033_);
v___x_3062_ = lean_box(v___x_3056_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3062_);
v___x_3064_ = v___x_3027_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
lean_dec(v_ctors_3033_);
v___x_3066_ = lean_box(v___x_3037_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3066_);
v___x_3068_ = v___x_3027_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
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
uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
lean_dec(v_ctors_3033_);
lean_dec(v_numIndices_3032_);
lean_dec(v_numParams_3031_);
lean_dec_ref(v_val_3029_);
v___x_3070_ = 0;
v___x_3071_ = lean_box(v___x_3070_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3071_);
v___x_3073_ = v___x_3027_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
uint8_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_dec(v_a_3025_);
v___x_3075_ = 0;
v___x_3076_ = lean_box(v___x_3075_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3076_);
v___x_3078_ = v___x_3027_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
v_a_3081_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3024_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3024_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1___boxed(lean_object* v_declName_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object* v_cfg_3094_, lean_object* v_declName_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
uint8_t v_structures_3099_; uint8_t v_enums_3100_; uint8_t v_a_3102_; 
v_structures_3099_ = lean_ctor_get_uint8(v_cfg_3094_, sizeof(void*)*3 + 5);
v_enums_3100_ = lean_ctor_get_uint8(v_cfg_3094_, sizeof(void*)*3 + 7);
if (v_enums_3100_ == 0)
{
v_a_3102_ = v_enums_3100_;
goto v___jp_3101_;
}
else
{
lean_object* v___x_3140_; 
lean_inc(v_declName_3095_);
v___x_3140_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_3095_, v_a_3096_, v_a_3097_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3151_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3151_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3151_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
uint8_t v___x_3145_; 
v___x_3145_ = lean_unbox(v_a_3141_);
if (v___x_3145_ == 0)
{
uint8_t v___x_3146_; 
lean_del_object(v___x_3143_);
v___x_3146_ = lean_unbox(v_a_3141_);
lean_dec(v_a_3141_);
v_a_3102_ = v___x_3146_;
goto v___jp_3101_;
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
lean_dec(v_a_3141_);
lean_dec(v_declName_3095_);
v___x_3147_ = lean_box(v_enums_3100_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v___x_3147_);
v___x_3149_ = v___x_3143_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
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
else
{
lean_dec(v_declName_3095_);
return v___x_3140_;
}
}
v___jp_3101_:
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_st_ref_get(v_a_3097_);
if (v_structures_3099_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v___x_3103_);
lean_dec(v_declName_3095_);
v___x_3104_ = lean_box(v_a_3102_);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
return v___x_3105_;
}
else
{
if (v_a_3102_ == 0)
{
lean_object* v_env_3106_; uint8_t v___x_3107_; 
v_env_3106_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_ref(v_env_3106_);
lean_dec(v___x_3103_);
lean_inc(v_declName_3095_);
v___x_3107_ = l_Lean_isStructure(v_env_3106_, v_declName_3095_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec(v_declName_3095_);
v___x_3108_ = lean_box(v_a_3102_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_3095_, v_a_3096_, v_a_3097_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3129_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3129_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3129_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
if (lean_obj_tag(v_a_3111_) == 5)
{
lean_object* v_val_3115_; uint8_t v_isRec_3116_; 
v_val_3115_ = lean_ctor_get(v_a_3111_, 0);
lean_inc_ref(v_val_3115_);
lean_dec_ref_known(v_a_3111_, 1);
v_isRec_3116_ = lean_ctor_get_uint8(v_val_3115_, sizeof(void*)*6);
lean_dec_ref(v_val_3115_);
if (v_isRec_3116_ == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = lean_box(v___x_3107_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3117_);
v___x_3119_ = v___x_3113_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = lean_box(v_a_3102_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3121_);
v___x_3123_ = v___x_3113_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
lean_dec(v_a_3111_);
v___x_3125_ = lean_box(v_a_3102_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3125_);
v___x_3127_ = v___x_3113_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
v_a_3130_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3110_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3110_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_dec(v___x_3103_);
lean_dec(v_declName_3095_);
v___x_3138_ = lean_box(v_a_3102_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType___boxed(lean_object* v_cfg_3152_, lean_object* v_declName_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3152_, v_declName_3153_, v_a_3154_, v_a_3155_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec_ref(v_cfg_3152_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(lean_object* v_00_u03b1_3158_, lean_object* v_constName_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_3159_, v___y_3160_, v___y_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3164_, lean_object* v_constName_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(v_00_u03b1_3164_, v_constName_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3170_, lean_object* v_ref_3171_, lean_object* v_constName_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_3171_, v_constName_3172_, v___y_3173_, v___y_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3177_, lean_object* v_ref_3178_, lean_object* v_constName_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(v_00_u03b1_3177_, v_ref_3178_, v_constName_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v_ref_3178_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3184_, lean_object* v_ref_3185_, lean_object* v_msg_3186_, lean_object* v_declHint_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3185_, v_msg_3186_, v_declHint_3187_, v___y_3188_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3192_, lean_object* v_ref_3193_, lean_object* v_msg_3194_, lean_object* v_declHint_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3192_, v_ref_3193_, v_msg_3194_, v_declHint_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v_ref_3193_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_3200_, lean_object* v_declHint_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_3200_, v_declHint_3201_, v___y_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3206_, lean_object* v_declHint_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3206_, v_declHint_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b1_3212_, lean_object* v_ref_3213_, lean_object* v_msg_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_3213_, v_msg_3214_, v___y_3215_, v___y_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b1_3219_, lean_object* v_ref_3220_, lean_object* v_msg_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03b1_3219_, v_ref_3220_, v_msg_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v_ref_3220_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b1_3226_, lean_object* v_msg_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_3227_, v___y_3228_, v___y_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3232_, lean_object* v_msg_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(v_00_u03b1_3232_, v_msg_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3237_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(lean_object* v_a_3238_, lean_object* v_as_3239_, size_t v_i_3240_, size_t v_stop_3241_){
_start:
{
uint8_t v___x_3242_; 
v___x_3242_ = lean_usize_dec_eq(v_i_3240_, v_stop_3241_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = lean_array_uget_borrowed(v_as_3239_, v_i_3240_);
v___x_3244_ = lean_name_eq(v_a_3238_, v___x_3243_);
if (v___x_3244_ == 0)
{
size_t v___x_3245_; size_t v___x_3246_; 
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_add(v_i_3240_, v___x_3245_);
v_i_3240_ = v___x_3246_;
goto _start;
}
else
{
return v___x_3244_;
}
}
else
{
uint8_t v___x_3248_; 
v___x_3248_ = 0;
return v___x_3248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0___boxed(lean_object* v_a_3249_, lean_object* v_as_3250_, lean_object* v_i_3251_, lean_object* v_stop_3252_){
_start:
{
size_t v_i_boxed_3253_; size_t v_stop_boxed_3254_; uint8_t v_res_3255_; lean_object* v_r_3256_; 
v_i_boxed_3253_ = lean_unbox_usize(v_i_3251_);
lean_dec(v_i_3251_);
v_stop_boxed_3254_ = lean_unbox_usize(v_stop_3252_);
lean_dec(v_stop_3252_);
v_res_3255_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3249_, v_as_3250_, v_i_boxed_3253_, v_stop_boxed_3254_);
lean_dec_ref(v_as_3250_);
lean_dec(v_a_3249_);
v_r_3256_ = lean_box(v_res_3255_);
return v_r_3256_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(lean_object* v_as_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = lean_array_get_size(v_as_3257_);
v___x_3261_ = lean_nat_dec_lt(v___x_3259_, v___x_3260_);
if (v___x_3261_ == 0)
{
return v___x_3261_;
}
else
{
if (v___x_3261_ == 0)
{
return v___x_3261_;
}
else
{
size_t v___x_3262_; size_t v___x_3263_; uint8_t v___x_3264_; 
v___x_3262_ = ((size_t)0ULL);
v___x_3263_ = lean_usize_of_nat(v___x_3260_);
v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3258_, v_as_3257_, v___x_3262_, v___x_3263_);
return v___x_3264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0___boxed(lean_object* v_as_3265_, lean_object* v_a_3266_){
_start:
{
uint8_t v_res_3267_; lean_object* v_r_3268_; 
v_res_3267_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_as_3265_, v_a_3266_);
lean_dec(v_a_3266_);
lean_dec_ref(v_as_3265_);
v_r_3268_ = lean_box(v_res_3267_);
return v_r_3268_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__0));
v___x_3271_ = l_Lean_stringToMessageData(v___x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(lean_object* v_cfg_3272_, lean_object* v_as_3273_, size_t v_sz_3274_, size_t v_i_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_a_3281_; uint8_t v___x_3285_; 
v___x_3285_ = lean_usize_dec_lt(v_i_3275_, v_sz_3274_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_b_3276_);
return v___x_3286_;
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_a_3287_ = lean_array_uget_borrowed(v_as_3273_, v_i_3275_);
v___x_3288_ = lean_box(0);
lean_inc(v_a_3287_);
v___x_3289_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_3287_, v___x_3288_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3294_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc_n(v_a_3290_, 2);
lean_dec_ref_known(v___x_3289_, 1);
v___x_3294_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3272_, v_a_3290_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; uint8_t v___x_3296_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref_known(v___x_3294_, 1);
v___x_3296_ = lean_unbox(v_a_3295_);
lean_dec(v_a_3295_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3297_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
lean_inc(v_a_3290_);
v___x_3298_ = l_Lean_MessageData_ofName(v_a_3290_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_a_3287_, v___x_3301_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_dec_ref_known(v___x_3302_, 1);
goto v___jp_3291_;
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_a_3290_);
lean_dec_ref(v_b_3276_);
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
goto v___jp_3291_;
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v_a_3290_);
lean_dec_ref(v_b_3276_);
v_a_3311_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3294_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3294_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
v___jp_3291_:
{
uint8_t v___x_3292_; 
v___x_3292_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_b_3276_, v_a_3290_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_array_push(v_b_3276_, v_a_3290_);
v_a_3281_ = v___x_3293_;
goto v___jp_3280_;
}
else
{
lean_dec(v_a_3290_);
v_a_3281_ = v_b_3276_;
goto v___jp_3280_;
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref(v_b_3276_);
v_a_3319_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3289_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3289_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
v___jp_3280_:
{
size_t v___x_3282_; size_t v___x_3283_; 
v___x_3282_ = ((size_t)1ULL);
v___x_3283_ = lean_usize_add(v_i_3275_, v___x_3282_);
v_i_3275_ = v___x_3283_;
v_b_3276_ = v_a_3281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___boxed(lean_object* v_cfg_3327_, lean_object* v_as_3328_, lean_object* v_sz_3329_, lean_object* v_i_3330_, lean_object* v_b_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
size_t v_sz_boxed_3335_; size_t v_i_boxed_3336_; lean_object* v_res_3337_; 
v_sz_boxed_3335_ = lean_unbox_usize(v_sz_3329_);
lean_dec(v_sz_3329_);
v_i_boxed_3336_ = lean_unbox_usize(v_i_3330_);
lean_dec(v_i_3330_);
v_res_3337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3327_, v_as_3328_, v_sz_boxed_3335_, v_i_boxed_3336_, v_b_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v_as_3328_);
lean_dec_ref(v_cfg_3327_);
return v_res_3337_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__3));
v___x_3347_ = l_Lean_stringToMessageData(v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object* v_stx_3350_, lean_object* v_cfg_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
if (lean_obj_tag(v_stx_3350_) == 1)
{
lean_object* v_val_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3390_; 
v_val_3355_ = lean_ctor_get(v_stx_3350_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_stx_3350_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3357_ = v_stx_3350_;
v_isShared_3358_ = v_isSharedCheck_3390_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_val_3355_);
lean_dec(v_stx_3350_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3390_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2));
lean_inc(v_val_3355_);
v___x_3360_ = l_Lean_Syntax_isOfKind(v_val_3355_, v___x_3359_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_del_object(v___x_3357_);
v___x_3361_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4);
v___x_3362_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_val_3355_, v___x_3361_, v_a_3352_, v_a_3353_);
lean_dec(v_val_3355_);
return v___x_3362_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v_ids_3365_; lean_object* v_types_3366_; lean_object* v___x_3367_; size_t v_sz_3368_; size_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3363_ = lean_unsigned_to_nat(2u);
v___x_3364_ = l_Lean_Syntax_getArg(v_val_3355_, v___x_3363_);
lean_dec(v_val_3355_);
v_ids_3365_ = l_Lean_Syntax_getArgs(v___x_3364_);
lean_dec(v___x_3364_);
v_types_3366_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__5));
v___x_3367_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ids_3365_);
lean_dec_ref(v_ids_3365_);
v_sz_3368_ = lean_array_size(v___x_3367_);
v___x_3369_ = ((size_t)0ULL);
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3351_, v___x_3367_, v_sz_3368_, v___x_3369_, v_types_3366_, v_a_3352_, v_a_3353_);
lean_dec_ref(v___x_3367_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3381_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3381_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3381_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v_a_3371_);
v___x_3376_ = v___x_3357_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3376_);
v___x_3378_ = v___x_3373_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_del_object(v___x_3357_);
v_a_3382_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3370_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3370_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec(v_stx_3350_);
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___boxed(lean_object* v_stx_3393_, lean_object* v_cfg_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_stx_3393_, v_cfg_3394_, v_a_3395_, v_a_3396_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_cfg_3394_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3414_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3411_, v___x_3412_, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2____boxed(lean_object* v_a_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_();
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3434_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3437_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3434_, v___x_3435_, v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2____boxed(lean_object* v_a_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3449_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3452_ = l_Lean_Meta_registerSimpAttr(v___x_3449_, v___x_3450_, v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2____boxed(lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(lean_object* v_e_3455_){
_start:
{
if (lean_obj_tag(v_e_3455_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3465_; 
v_a_3457_ = lean_ctor_get(v_e_3455_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_e_3455_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3459_ = v_e_3455_;
v_isShared_3460_ = v_isSharedCheck_3465_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v_e_3455_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3465_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_mk_io_user_error(v_a_3457_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 1);
lean_ctor_set(v___x_3459_, 0, v___x_3461_);
v___x_3463_ = v___x_3459_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
v_a_3466_ = lean_ctor_get(v_e_3455_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_e_3455_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v_e_3455_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v_e_3455_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
lean_ctor_set_tag(v___x_3468_, 0);
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_e_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3477_, lean_object* v_e_3478_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3478_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3481_, lean_object* v_e_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(v_00_u03b1_3481_, v_e_3482_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v_declName_3485_, lean_object* v_stx_3486_, uint8_t v_attrKind_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v___x_3491_; lean_object* v_env_3492_; lean_object* v_ref_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3491_ = lean_st_ref_get(v___y_3489_);
v_env_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc_ref_n(v_env_3492_, 2);
lean_dec(v___x_3491_);
v_ref_3493_ = lean_ctor_get(v___y_3488_, 2);
v___x_3494_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3495_ = l_Lean_getAttributeImpl(v_env_3492_, v___x_3494_);
v___x_3496_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v_add_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v_add_3498_ = lean_ctor_get(v_a_3497_, 1);
lean_inc_ref(v_add_3498_);
lean_dec(v_a_3497_);
v___x_3499_ = lean_box(v_attrKind_3487_);
lean_inc(v___y_3489_);
lean_inc_ref(v___y_3488_);
lean_inc(v_stx_3486_);
lean_inc(v_declName_3485_);
v___x_3500_ = lean_apply_6(v_add_3498_, v_declName_3485_, v_stx_3486_, v___x_3499_, v___y_3488_, v___y_3489_, lean_box(0));
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3525_; 
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; 
v_unused_3526_ = lean_ctor_get(v___x_3500_, 0);
lean_dec(v_unused_3526_);
v___x_3502_ = v___x_3500_;
v_isShared_3503_ = v_isSharedCheck_3525_;
goto v_resetjp_3501_;
}
else
{
lean_dec(v___x_3500_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3525_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3505_ = l_Lean_getAttributeImpl(v_env_3492_, v___x_3504_);
v___x_3506_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3505_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v_add_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_del_object(v___x_3502_);
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v___x_3506_, 1);
v_add_3508_ = lean_ctor_get(v_a_3507_, 1);
lean_inc_ref(v_add_3508_);
lean_dec(v_a_3507_);
v___x_3509_ = lean_box(v_attrKind_3487_);
lean_inc(v___y_3489_);
lean_inc_ref(v___y_3488_);
v___x_3510_ = lean_apply_6(v_add_3508_, v_declName_3485_, v_stx_3486_, v___x_3509_, v___y_3488_, v___y_3489_, lean_box(0));
return v___x_3510_;
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v_stx_3486_);
lean_dec(v_declName_3485_);
v_a_3511_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3513_ = v___x_3506_;
v_isShared_3514_ = v_isSharedCheck_3524_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3506_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3524_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3515_ = lean_io_error_to_string(v_a_3511_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set_tag(v___x_3502_, 3);
lean_ctor_set(v___x_3502_, 0, v___x_3515_);
v___x_3517_ = v___x_3502_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3521_; 
v___x_3518_ = l_Lean_MessageData_ofFormat(v___x_3517_);
lean_inc(v_ref_3493_);
v___x_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3519_, 0, v_ref_3493_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3519_);
v___x_3521_ = v___x_3513_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_3492_);
lean_dec(v_stx_3486_);
lean_dec(v_declName_3485_);
return v___x_3500_;
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v_env_3492_);
lean_dec(v_stx_3486_);
lean_dec(v_declName_3485_);
v_a_3527_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3529_ = v___x_3496_;
v_isShared_3530_ = v_isSharedCheck_3538_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3496_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3538_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3531_ = lean_io_error_to_string(v_a_3527_);
v___x_3532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
v___x_3533_ = l_Lean_MessageData_ofFormat(v___x_3532_);
lean_inc(v_ref_3493_);
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v_ref_3493_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3534_);
v___x_3536_ = v___x_3529_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_declName_3539_, lean_object* v_stx_3540_, lean_object* v_attrKind_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
uint8_t v_attrKind_boxed_3545_; lean_object* v_res_3546_; 
v_attrKind_boxed_3545_ = lean_unbox(v_attrKind_3541_);
v_res_3546_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v_declName_3539_, v_stx_3540_, v_attrKind_boxed_3545_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
return v_res_3546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3549_ = l_Lean_stringToMessageData(v___x_3548_);
return v___x_3549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3552_ = l_Lean_stringToMessageData(v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v___x_3553_, lean_object* v_decl_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3559_ = l_Lean_MessageData_ofName(v___x_3553_);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v___x_3562_, v___y_3555_, v___y_3556_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v___x_3564_, lean_object* v_decl_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v___x_3564_, v_decl_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v_decl_3565_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3600_ = l_Lean_registerBuiltinAttribute(v___x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
return v_res_3602_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_();
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
res = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_();
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
