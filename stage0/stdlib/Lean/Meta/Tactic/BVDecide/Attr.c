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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
lean_object* v___x_401_; lean_object* v_env_402_; uint8_t v___x_403_; lean_object* v_env_404_; lean_object* v___x_405_; lean_object* v_toCold_406_; lean_object* v_mctx_407_; lean_object* v_lctx_408_; lean_object* v_options_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_401_ = lean_st_ref_get(v___y_399_);
v_env_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_401_);
v___x_403_ = 0;
v_env_404_ = l_Lean_Environment_setRecordingDeps(v_env_402_, v___x_403_);
v___x_405_ = lean_st_ref_get(v___y_397_);
v_toCold_406_ = lean_ctor_get(v___y_398_, 0);
v_mctx_407_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_mctx_407_);
lean_dec(v___x_405_);
v_lctx_408_ = lean_ctor_get(v___y_396_, 2);
v_options_409_ = lean_ctor_get(v_toCold_406_, 2);
lean_inc_ref(v_options_409_);
lean_inc_ref(v_lctx_408_);
v___x_410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_410_, 0, v_env_404_);
lean_ctor_set(v___x_410_, 1, v_mctx_407_);
lean_ctor_set(v___x_410_, 2, v_lctx_408_);
lean_ctor_set(v___x_410_, 3, v_options_409_);
v___x_411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_msgData_395_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msgData_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object* v_msg_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_ref_426_; lean_object* v___x_427_; lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_ref_426_ = lean_ctor_get(v___y_423_, 2);
v___x_427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_436_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v_ref_426_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v_ref_426_);
lean_ctor_set(v___x_432_, 1, v_a_428_);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 1);
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(lean_object* v_ctor_447_, lean_object* v_args_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_467_ = lean_string_dec_eq(v_ctor_447_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_469_ = lean_string_dec_eq(v_ctor_447_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_471_ = lean_string_dec_eq(v_ctor_447_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_array_get_size(v_args_448_);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v___x_476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_477_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_476_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
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
goto v___jp_454_;
}
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_array_get_size(v_args_448_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_490_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_489_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
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
goto v___jp_458_;
}
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_array_get_size(v_args_448_);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v___x_502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_503_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_502_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
goto v___jp_462_;
}
}
v___jp_454_:
{
uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = 0;
v___x_456_ = lean_box(v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
v___jp_458_:
{
uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = 2;
v___x_460_ = lean_box(v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
v___jp_462_:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = 1;
v___x_464_ = lean_box(v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object* v_ctor_512_, lean_object* v_args_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(v_ctor_512_, v_args_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v_args_513_);
lean_dec_ref(v_ctor_512_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___f_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0));
v___x_528_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_529_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_528_, v___f_527_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___boxed(lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(lean_object* v_00_u03b1_537_, lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_545_, lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(v_00_u03b1_545_, v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0));
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode(void){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object* v___x_561_, lean_object* v_ctor_562_, lean_object* v_args_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0));
v___x_771_ = lean_string_dec_eq(v_ctor_562_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_array_get_size(v_args_563_);
v___x_774_ = lean_unsigned_to_nat(15u);
v___x_775_ = lean_nat_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_777_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_776_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
else
{
goto v___jp_569_;
}
}
v___jp_569_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_570_);
lean_inc(v___x_571_);
v___x_572_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_571_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_574_);
lean_inc(v___x_575_);
v___x_576_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_575_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_576_, 1);
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_578_);
lean_inc(v___x_579_);
v___x_580_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_579_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = lean_unsigned_to_nat(3u);
v___x_583_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_582_);
lean_inc(v___x_583_);
v___x_584_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_583_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_unsigned_to_nat(4u);
v___x_587_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_586_);
lean_inc(v___x_587_);
v___x_588_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_587_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = lean_unsigned_to_nat(5u);
v___x_591_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_590_);
lean_inc(v___x_591_);
v___x_592_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_591_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = lean_unsigned_to_nat(6u);
v___x_595_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_594_);
lean_inc(v___x_595_);
v___x_596_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_595_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = lean_unsigned_to_nat(7u);
v___x_599_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_598_);
lean_inc(v___x_599_);
v___x_600_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_599_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = lean_unsigned_to_nat(8u);
v___x_603_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_602_);
lean_inc(v___x_603_);
v___x_604_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_603_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = lean_unsigned_to_nat(9u);
v___x_607_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_606_);
lean_inc(v___x_607_);
v___x_608_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_607_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = lean_unsigned_to_nat(10u);
v___x_611_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_610_);
lean_inc(v___x_611_);
v___x_612_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_611_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = lean_unsigned_to_nat(11u);
v___x_615_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_614_);
lean_inc(v___x_615_);
v___x_616_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_615_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = lean_unsigned_to_nat(12u);
v___x_619_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_618_);
lean_inc(v___x_619_);
v___x_620_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v___x_619_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = lean_unsigned_to_nat(13u);
v___x_623_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_622_);
lean_inc(v___x_623_);
v___x_624_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_623_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_unsigned_to_nat(14u);
v___x_627_ = lean_array_get_borrowed(v___x_561_, v_args_563_, v___x_626_);
lean_inc(v___x_627_);
v___x_628_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_627_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_649_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_649_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_649_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_649_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; uint8_t v___x_634_; uint8_t v___x_635_; uint8_t v___x_636_; uint8_t v___x_637_; uint8_t v___x_638_; uint8_t v___x_639_; uint8_t v___x_640_; uint8_t v___x_641_; uint8_t v___x_642_; uint8_t v___x_643_; uint8_t v___x_644_; uint8_t v___x_645_; lean_object* v___x_647_; 
v___x_633_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v___x_633_, 0, v_a_573_);
lean_ctor_set(v___x_633_, 1, v_a_613_);
lean_ctor_set(v___x_633_, 2, v_a_629_);
v___x_634_ = lean_unbox(v_a_577_);
lean_dec(v_a_577_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3, v___x_634_);
v___x_635_ = lean_unbox(v_a_581_);
lean_dec(v_a_581_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 1, v___x_635_);
v___x_636_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 2, v___x_636_);
v___x_637_ = lean_unbox(v_a_589_);
lean_dec(v_a_589_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 3, v___x_637_);
v___x_638_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 4, v___x_638_);
v___x_639_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 5, v___x_639_);
v___x_640_ = lean_unbox(v_a_601_);
lean_dec(v_a_601_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 6, v___x_640_);
v___x_641_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 7, v___x_641_);
v___x_642_ = lean_unbox(v_a_609_);
lean_dec(v_a_609_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 8, v___x_642_);
v___x_643_ = lean_unbox(v_a_617_);
lean_dec(v_a_617_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 9, v___x_643_);
v___x_644_ = lean_unbox(v_a_621_);
lean_dec(v_a_621_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 10, v___x_644_);
v___x_645_ = lean_unbox(v_a_625_);
lean_dec(v_a_625_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 11, v___x_645_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_647_ = v___x_631_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_633_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_a_625_);
lean_dec(v_a_621_);
lean_dec(v_a_617_);
lean_dec(v_a_613_);
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_650_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_628_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_628_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_a_621_);
lean_dec(v_a_617_);
lean_dec(v_a_613_);
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_658_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_624_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_624_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v_a_617_);
lean_dec(v_a_613_);
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_666_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_620_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_620_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_a_613_);
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_674_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_616_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_616_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_682_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_612_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_612_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_690_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_608_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_608_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_698_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_604_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_604_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_706_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_600_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_600_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_a_593_);
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_714_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_596_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_596_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_589_);
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_722_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_592_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_592_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_a_585_);
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_730_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_588_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_588_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_581_);
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_738_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_584_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_584_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_a_577_);
lean_dec(v_a_573_);
v_a_746_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_580_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_580_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_573_);
v_a_754_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_576_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_576_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_572_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_572_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object* v___x_786_, lean_object* v_ctor_787_, lean_object* v_args_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(v___x_786_, v_ctor_787_, v_args_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_args_788_);
lean_dec_ref(v_ctor_787_);
lean_dec_ref(v___x_786_);
return v_res_794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_795_; lean_object* v___f_796_; 
v___x_795_ = l_Lean_instInhabitedExpr;
v___f_796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_796_, 0, v___x_795_);
return v___f_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___f_810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0);
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_812_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_811_, v___f_810_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_819_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_box(0);
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_823_ = l_Lean_Expr_const___override(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0));
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig(void){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_box(0);
v___x_831_ = l_Lean_Elab_abortTermExceptionId;
v___x_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg(){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v_res_837_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_box(1);
v___x_839_ = l_Lean_MessageData_ofFormat(v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2));
v___x_844_ = l_Lean_MessageData_ofFormat(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
return v_x_845_;
}
else
{
lean_object* v_head_847_; lean_object* v_tail_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_870_; 
v_head_847_ = lean_ctor_get(v_x_846_, 0);
v_tail_848_ = lean_ctor_get(v_x_846_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_846_);
if (v_isSharedCheck_870_ == 0)
{
v___x_850_ = v_x_846_;
v_isShared_851_ = v_isSharedCheck_870_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_tail_848_);
lean_inc(v_head_847_);
lean_dec(v_x_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_870_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_before_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_868_; 
v_before_852_ = lean_ctor_get(v_head_847_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v_head_847_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_head_847_, 1);
lean_dec(v_unused_869_);
v___x_854_ = v_head_847_;
v_isShared_855_ = v_isSharedCheck_868_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_before_852_);
lean_dec(v_head_847_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_868_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 7);
lean_ctor_set(v___x_854_, 1, v___x_856_);
lean_ctor_set(v___x_854_, 0, v_x_845_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_x_845_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_867_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3);
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 7);
lean_ctor_set(v___x_850_, 1, v___x_859_);
lean_ctor_set(v___x_850_, 0, v___x_858_);
v___x_861_ = v___x_850_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_866_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = l_Lean_MessageData_ofSyntax(v_before_852_);
v___x_863_ = l_Lean_indentD(v___x_862_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_861_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v_x_845_ = v___x_864_;
v_x_846_ = v_tail_848_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object* v_opts_871_, lean_object* v_opt_872_){
_start:
{
lean_object* v_name_873_; lean_object* v_defValue_874_; lean_object* v_map_875_; lean_object* v___x_876_; 
v_name_873_ = lean_ctor_get(v_opt_872_, 0);
v_defValue_874_ = lean_ctor_get(v_opt_872_, 1);
v_map_875_ = lean_ctor_get(v_opts_871_, 0);
v___x_876_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_875_, v_name_873_);
if (lean_obj_tag(v___x_876_) == 0)
{
uint8_t v___x_877_; 
v___x_877_ = lean_unbox(v_defValue_874_);
return v___x_877_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v___x_876_, 1);
if (lean_obj_tag(v_val_878_) == 1)
{
uint8_t v_v_879_; 
v_v_879_ = lean_ctor_get_uint8(v_val_878_, 0);
lean_dec_ref_known(v_val_878_, 0);
return v_v_879_;
}
else
{
uint8_t v___x_880_; 
lean_dec(v_val_878_);
v___x_880_ = lean_unbox(v_defValue_874_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object* v_opts_881_, lean_object* v_opt_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_opts_881_, v_opt_882_);
lean_dec_ref(v_opt_882_);
lean_dec_ref(v_opts_881_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1));
v___x_889_ = l_Lean_MessageData_ofFormat(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object* v_msgData_890_, lean_object* v_macroStack_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_894_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_892_);
v___x_895_ = l_Lean_Elab_pp_macroStack;
v___x_896_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v___x_894_, v___x_895_);
lean_dec_ref(v___x_894_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec(v_macroStack_891_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_msgData_890_);
return v___x_897_;
}
else
{
if (lean_obj_tag(v_macroStack_891_) == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_msgData_890_);
return v___x_898_;
}
else
{
lean_object* v_head_899_; lean_object* v_after_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_915_; 
v_head_899_ = lean_ctor_get(v_macroStack_891_, 0);
lean_inc(v_head_899_);
v_after_900_ = lean_ctor_get(v_head_899_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_head_899_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_head_899_, 0);
lean_dec(v_unused_916_);
v___x_902_ = v_head_899_;
v_isShared_903_ = v_isSharedCheck_915_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_after_900_);
lean_dec(v_head_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_915_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 7);
lean_ctor_set(v___x_902_, 1, v___x_904_);
lean_ctor_set(v___x_902_, 0, v_msgData_890_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_msgData_890_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_914_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_msgData_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_907_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_MessageData_ofSyntax(v_after_900_);
v___x_910_ = l_Lean_indentD(v___x_909_);
v_msgData_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_911_, 0, v___x_908_);
lean_ctor_set(v_msgData_911_, 1, v___x_910_);
v___x_912_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(v_msgData_911_, v_macroStack_891_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_msgData_917_, lean_object* v_macroStack_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_917_, v_macroStack_918_, v___y_919_);
lean_dec_ref(v___y_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_ref_930_; lean_object* v_macroStack_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
v_ref_930_ = lean_ctor_get(v___y_927_, 2);
v_macroStack_931_ = lean_ctor_get(v___y_923_, 1);
v___x_932_ = l_Lean_Elab_getBetterRef(v_ref_930_, v_macroStack_931_);
v___x_933_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_922_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
lean_inc(v_macroStack_931_);
v___x_935_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_a_934_, v_macroStack_931_, v___y_927_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_932_);
lean_ctor_set(v___x_940_, 1, v_a_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 1);
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object* v_msg_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object* v_e_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = l_Lean_Expr_hasMVar(v_e_954_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_e_954_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v_mctx_960_; lean_object* v___x_961_; lean_object* v_fst_962_; lean_object* v_snd_963_; lean_object* v___x_964_; lean_object* v_cache_965_; lean_object* v_zetaDeltaFVarIds_966_; lean_object* v_postponed_967_; lean_object* v_diag_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v___x_959_ = lean_st_ref_get(v___y_955_);
v_mctx_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_mctx_960_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_instantiateMVarsCore(v_mctx_960_, v_e_954_);
v_fst_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_fst_962_);
v_snd_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v___x_961_);
v___x_964_ = lean_st_ref_take(v___y_955_);
v_cache_965_ = lean_ctor_get(v___x_964_, 1);
v_zetaDeltaFVarIds_966_ = lean_ctor_get(v___x_964_, 2);
v_postponed_967_ = lean_ctor_get(v___x_964_, 3);
v_diag_968_ = lean_ctor_get(v___x_964_, 4);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___x_964_, 0);
lean_dec(v_unused_978_);
v___x_970_ = v___x_964_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_diag_968_);
lean_inc(v_postponed_967_);
lean_inc(v_zetaDeltaFVarIds_966_);
lean_inc(v_cache_965_);
lean_dec(v___x_964_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_snd_963_);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_snd_963_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_cache_965_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_zetaDeltaFVarIds_966_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_postponed_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_diag_968_);
v___x_973_ = v_reuseFailAlloc_976_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_st_ref_put(v___y_955_, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_fst_962_);
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object* v_e_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_979_, v___y_980_);
lean_dec(v___y_980_);
return v_res_982_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_987_ = l_Lean_MessageData_ofExpr(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2);
v___x_989_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_995_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(lean_object* v_stx_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_ty_x3f_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_toCold_1017_; lean_object* v_currRecDepth_1018_; lean_object* v_ref_1019_; uint16_t v_optionFlags_1020_; uint8_t v_suppressElabErrors_1021_; uint8_t v_checkDeprecated_1022_; uint8_t v_isRecordingDeps_1023_; uint8_t v___x_1024_; lean_object* v_ref_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_ty_x3f_1011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_1012_ = 1;
v___x_1013_ = lean_box(0);
v___x_1014_ = lean_box(v___x_1012_);
v___x_1015_ = lean_box(v___x_1012_);
lean_inc(v_stx_1003_);
v___x_1016_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1016_, 0, v_stx_1003_);
lean_closure_set(v___x_1016_, 1, v_ty_x3f_1011_);
lean_closure_set(v___x_1016_, 2, v___x_1014_);
lean_closure_set(v___x_1016_, 3, v___x_1015_);
lean_closure_set(v___x_1016_, 4, v___x_1013_);
v_toCold_1017_ = lean_ctor_get(v_a_1008_, 0);
v_currRecDepth_1018_ = lean_ctor_get(v_a_1008_, 1);
v_ref_1019_ = lean_ctor_get(v_a_1008_, 2);
v_optionFlags_1020_ = lean_ctor_get_uint16(v_a_1008_, sizeof(void*)*3);
v_suppressElabErrors_1021_ = lean_ctor_get_uint8(v_a_1008_, sizeof(void*)*3 + 2);
v_checkDeprecated_1022_ = lean_ctor_get_uint8(v_a_1008_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1023_ = lean_ctor_get_uint8(v_a_1008_, sizeof(void*)*3 + 4);
v___x_1024_ = 1;
v_ref_1025_ = l_Lean_replaceRef(v_stx_1003_, v_ref_1019_);
lean_dec(v_stx_1003_);
lean_inc(v_currRecDepth_1018_);
lean_inc_ref(v_toCold_1017_);
v___x_1026_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1026_, 0, v_toCold_1017_);
lean_ctor_set(v___x_1026_, 1, v_currRecDepth_1018_);
lean_ctor_set(v___x_1026_, 2, v_ref_1025_);
lean_ctor_set_uint16(v___x_1026_, sizeof(void*)*3, v_optionFlags_1020_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*3 + 2, v_suppressElabErrors_1021_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*3 + 3, v_checkDeprecated_1022_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*3 + 4, v_isRecordingDeps_1023_);
v___x_1027_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1016_, v___x_1024_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v___x_1026_, v_a_1009_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v_a_1030_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; uint8_t v___x_1114_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1028_, v_a_1007_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
v___x_1114_ = l_Lean_Expr_hasSorry(v_a_1030_);
if (v___x_1114_ == 0)
{
v___y_1059_ = v_a_1004_;
v___y_1060_ = v_a_1005_;
v___y_1061_ = v_a_1006_;
v___y_1062_ = v_a_1007_;
v___y_1063_ = v___x_1026_;
v___y_1064_ = v_a_1009_;
goto v___jp_1058_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_Expr_hasSyntheticSorry(v_a_1030_);
if (v___x_1115_ == 0)
{
v___y_1096_ = v_a_1004_;
v___y_1097_ = v_a_1005_;
v___y_1098_ = v_a_1006_;
v___y_1099_ = v_a_1007_;
v___y_1100_ = v___x_1026_;
v___y_1101_ = v_a_1009_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_a_1030_);
lean_dec_ref_known(v___x_1026_, 3);
v___x_1116_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
v___jp_1031_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1030_);
v___x_1039_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_1030_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_dec_ref(v___y_1036_);
lean_dec(v_a_1030_);
return v___x_1039_;
}
else
{
lean_object* v_a_1040_; uint8_t v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
v___x_1041_ = l_Lean_Exception_isInterrupt(v_a_1040_);
if (v___x_1041_ == 0)
{
uint8_t v___x_1042_; 
lean_inc(v_a_1040_);
v___x_1042_ = l_Lean_Exception_isRuntime(v_a_1040_);
if (v___x_1042_ == 0)
{
if (lean_obj_tag(v_a_1040_) == 0)
{
lean_dec_ref_known(v_a_1040_, 2);
lean_dec_ref(v___y_1036_);
lean_dec(v_a_1030_);
return v___x_1039_;
}
else
{
lean_object* v_id_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1056_; 
v_id_1043_ = lean_ctor_get(v_a_1040_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_a_1040_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v_a_1040_, 1);
lean_dec(v_unused_1057_);
v___x_1045_ = v_a_1040_;
v_isShared_1046_ = v_isSharedCheck_1056_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_id_1043_);
lean_dec(v_a_1040_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1056_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
uint8_t v___x_1047_; 
v___x_1047_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1038_, v_id_1043_);
lean_dec(v_id_1043_);
if (v___x_1047_ == 0)
{
lean_del_object(v___x_1045_);
lean_dec_ref(v___y_1036_);
lean_dec(v_a_1030_);
return v___x_1039_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_dec_ref_known(v___x_1039_, 1);
v___x_1048_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6);
v___x_1049_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1050_ = l_Lean_indentExpr(v_a_1030_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 7);
lean_ctor_set(v___x_1045_, 1, v___x_1050_);
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1052_ = v___x_1045_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_1048_);
v___x_1054_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1053_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec_ref(v___y_1036_);
return v___x_1054_;
}
}
}
}
}
else
{
lean_dec(v_a_1040_);
lean_dec_ref(v___y_1036_);
lean_dec(v_a_1030_);
return v___x_1039_;
}
}
else
{
lean_dec(v_a_1040_);
lean_dec_ref(v___y_1036_);
lean_dec(v_a_1030_);
return v___x_1039_;
}
}
}
v___jp_1058_:
{
lean_object* v___x_1065_; 
lean_inc(v_a_1030_);
v___x_1065_ = l_Lean_Meta_getMVars(v_a_1030_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1066_, v___x_1013_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v_a_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; uint8_t v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = lean_unbox(v_a_1068_);
lean_dec(v_a_1068_);
if (v___x_1069_ == 0)
{
v___y_1032_ = v___y_1059_;
v___y_1033_ = v___y_1060_;
v___y_1034_ = v___y_1061_;
v___y_1035_ = v___y_1062_;
v___y_1036_ = v___y_1063_;
v___y_1037_ = v___y_1064_;
goto v___jp_1031_;
}
else
{
lean_object* v___x_1070_; lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v___y_1063_);
lean_dec(v_a_1030_);
v___x_1070_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v___y_1063_);
lean_dec(v_a_1030_);
v_a_1079_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1067_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1067_);
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
lean_dec_ref(v___y_1063_);
lean_dec(v_a_1030_);
v_a_1087_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1065_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1065_);
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
v___jp_1095_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v___x_1102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1103_ = l_Lean_indentExpr(v_a_1030_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1104_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___y_1100_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
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
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref_known(v___x_1026_, 3);
v_a_1125_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1027_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1027_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_stx_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_1143_ = l_Lean_MessageData_ofExpr(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0);
v___x_1145_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1148_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set(v___x_1149_, 1, v___x_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_ty_x3f_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_toCold_1164_; lean_object* v_currRecDepth_1165_; lean_object* v_ref_1166_; uint16_t v_optionFlags_1167_; uint8_t v_suppressElabErrors_1168_; uint8_t v_checkDeprecated_1169_; uint8_t v_isRecordingDeps_1170_; uint8_t v___x_1171_; lean_object* v_ref_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_ty_x3f_1158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_1159_ = 1;
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_box(v___x_1159_);
v___x_1162_ = lean_box(v___x_1159_);
lean_inc(v_stx_1150_);
v___x_1163_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1163_, 0, v_stx_1150_);
lean_closure_set(v___x_1163_, 1, v_ty_x3f_1158_);
lean_closure_set(v___x_1163_, 2, v___x_1161_);
lean_closure_set(v___x_1163_, 3, v___x_1162_);
lean_closure_set(v___x_1163_, 4, v___x_1160_);
v_toCold_1164_ = lean_ctor_get(v_a_1155_, 0);
v_currRecDepth_1165_ = lean_ctor_get(v_a_1155_, 1);
v_ref_1166_ = lean_ctor_get(v_a_1155_, 2);
v_optionFlags_1167_ = lean_ctor_get_uint16(v_a_1155_, sizeof(void*)*3);
v_suppressElabErrors_1168_ = lean_ctor_get_uint8(v_a_1155_, sizeof(void*)*3 + 2);
v_checkDeprecated_1169_ = lean_ctor_get_uint8(v_a_1155_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1170_ = lean_ctor_get_uint8(v_a_1155_, sizeof(void*)*3 + 4);
v___x_1171_ = 1;
v_ref_1172_ = l_Lean_replaceRef(v_stx_1150_, v_ref_1166_);
lean_dec(v_stx_1150_);
lean_inc(v_currRecDepth_1165_);
lean_inc_ref(v_toCold_1164_);
v___x_1173_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1173_, 0, v_toCold_1164_);
lean_ctor_set(v___x_1173_, 1, v_currRecDepth_1165_);
lean_ctor_set(v___x_1173_, 2, v_ref_1172_);
lean_ctor_set_uint16(v___x_1173_, sizeof(void*)*3, v_optionFlags_1167_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*3 + 2, v_suppressElabErrors_1168_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*3 + 3, v_checkDeprecated_1169_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*3 + 4, v_isRecordingDeps_1170_);
v___x_1174_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1163_, v___x_1171_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v___x_1173_, v_a_1156_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v_a_1177_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; uint8_t v___x_1261_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1175_, v_a_1154_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref(v___x_1176_);
v___x_1261_ = l_Lean_Expr_hasSorry(v_a_1177_);
if (v___x_1261_ == 0)
{
v___y_1206_ = v_a_1151_;
v___y_1207_ = v_a_1152_;
v___y_1208_ = v_a_1153_;
v___y_1209_ = v_a_1154_;
v___y_1210_ = v___x_1173_;
v___y_1211_ = v_a_1156_;
goto v___jp_1205_;
}
else
{
uint8_t v___x_1262_; 
v___x_1262_ = l_Lean_Expr_hasSyntheticSorry(v_a_1177_);
if (v___x_1262_ == 0)
{
v___y_1243_ = v_a_1151_;
v___y_1244_ = v_a_1152_;
v___y_1245_ = v_a_1153_;
v___y_1246_ = v_a_1154_;
v___y_1247_ = v___x_1173_;
v___y_1248_ = v_a_1156_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1263_; lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_a_1177_);
lean_dec_ref_known(v___x_1173_, 3);
v___x_1263_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
v___jp_1178_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1177_);
v___x_1186_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_1177_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1177_);
return v___x_1186_;
}
else
{
lean_object* v_a_1187_; uint8_t v___x_1188_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
v___x_1188_ = l_Lean_Exception_isInterrupt(v_a_1187_);
if (v___x_1188_ == 0)
{
uint8_t v___x_1189_; 
lean_inc(v_a_1187_);
v___x_1189_ = l_Lean_Exception_isRuntime(v_a_1187_);
if (v___x_1189_ == 0)
{
if (lean_obj_tag(v_a_1187_) == 0)
{
lean_dec_ref_known(v_a_1187_, 2);
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1177_);
return v___x_1186_;
}
else
{
lean_object* v_id_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1203_; 
v_id_1190_ = lean_ctor_get(v_a_1187_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1187_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_a_1187_, 1);
lean_dec(v_unused_1204_);
v___x_1192_ = v_a_1187_;
v_isShared_1193_ = v_isSharedCheck_1203_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_id_1190_);
lean_dec(v_a_1187_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1203_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
uint8_t v___x_1194_; 
v___x_1194_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1185_, v_id_1190_);
lean_dec(v_id_1190_);
if (v___x_1194_ == 0)
{
lean_del_object(v___x_1192_);
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1177_);
return v___x_1186_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_dec_ref_known(v___x_1186_, 1);
v___x_1195_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_1196_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1197_ = l_Lean_indentExpr(v_a_1177_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set_tag(v___x_1192_, 7);
lean_ctor_set(v___x_1192_, 1, v___x_1197_);
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1199_ = v___x_1192_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1195_);
v___x_1201_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1200_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec_ref(v___y_1183_);
return v___x_1201_;
}
}
}
}
}
else
{
lean_dec(v_a_1187_);
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1177_);
return v___x_1186_;
}
}
else
{
lean_dec(v_a_1187_);
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1177_);
return v___x_1186_;
}
}
}
v___jp_1205_:
{
lean_object* v___x_1212_; 
lean_inc(v_a_1177_);
v___x_1212_ = l_Lean_Meta_getMVars(v_a_1177_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1213_, v___x_1160_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v_a_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; uint8_t v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = lean_unbox(v_a_1215_);
lean_dec(v_a_1215_);
if (v___x_1216_ == 0)
{
v___y_1179_ = v___y_1206_;
v___y_1180_ = v___y_1207_;
v___y_1181_ = v___y_1208_;
v___y_1182_ = v___y_1209_;
v___y_1183_ = v___y_1210_;
v___y_1184_ = v___y_1211_;
goto v___jp_1178_;
}
else
{
lean_object* v___x_1217_; lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v___y_1210_);
lean_dec(v_a_1177_);
v___x_1217_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v___y_1210_);
lean_dec(v_a_1177_);
v_a_1226_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1214_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1214_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v___y_1210_);
lean_dec(v_a_1177_);
v_a_1234_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1212_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1212_);
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
v___jp_1242_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v___x_1249_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1250_ = l_Lean_indentExpr(v_a_1177_);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1251_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___y_1247_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref_known(v___x_1173_, 3);
v_a_1272_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1174_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1174_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(lean_object* v_stx_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_toCold_1297_; lean_object* v_currRecDepth_1298_; lean_object* v_ref_1299_; uint16_t v_optionFlags_1300_; uint8_t v_suppressElabErrors_1301_; uint8_t v_checkDeprecated_1302_; uint8_t v_isRecordingDeps_1303_; lean_object* v___x_1304_; lean_object* v_ref_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_toCold_1297_ = lean_ctor_get(v_a_1294_, 0);
v_currRecDepth_1298_ = lean_ctor_get(v_a_1294_, 1);
v_ref_1299_ = lean_ctor_get(v_a_1294_, 2);
v_optionFlags_1300_ = lean_ctor_get_uint16(v_a_1294_, sizeof(void*)*3);
v_suppressElabErrors_1301_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*3 + 2);
v_checkDeprecated_1302_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1303_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*3 + 4);
v___x_1304_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1305_ = l_Lean_replaceRef(v_stx_1289_, v_ref_1299_);
lean_inc(v_currRecDepth_1298_);
lean_inc_ref(v_toCold_1297_);
v___x_1306_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1306_, 0, v_toCold_1297_);
lean_ctor_set(v___x_1306_, 1, v_currRecDepth_1298_);
lean_ctor_set(v___x_1306_, 2, v_ref_1305_);
lean_ctor_set_uint16(v___x_1306_, sizeof(void*)*3, v_optionFlags_1300_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3 + 2, v_suppressElabErrors_1301_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3 + 3, v_checkDeprecated_1302_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*3 + 4, v_isRecordingDeps_1303_);
lean_inc(v_stx_1289_);
v___x_1307_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_stx_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v___x_1306_, v_a_1295_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref_known(v___x_1306_, 3);
lean_dec(v_stx_1289_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_fst_1312_; lean_object* v___x_1314_; 
v_fst_1312_ = lean_ctor_get(v_a_1308_, 0);
lean_inc(v_fst_1312_);
lean_dec(v_a_1308_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_fst_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_fst_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1329_; 
v_a_1317_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1319_ = v___x_1307_;
v_isShared_1320_ = v_isSharedCheck_1329_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1329_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
lean_inc(v_a_1317_);
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
uint8_t v___x_1323_; 
v___x_1323_ = l_Lean_Exception_isInterrupt(v_a_1317_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
lean_inc(v_a_1317_);
v___x_1324_ = l_Lean_Exception_isRuntime(v_a_1317_);
if (v___x_1324_ == 0)
{
if (lean_obj_tag(v_a_1317_) == 0)
{
lean_dec_ref_known(v_a_1317_, 2);
lean_dec_ref_known(v___x_1306_, 3);
lean_dec(v_stx_1289_);
return v___x_1322_;
}
else
{
lean_object* v_id_1325_; uint8_t v___x_1326_; 
v_id_1325_ = lean_ctor_get(v_a_1317_, 0);
lean_inc(v_id_1325_);
lean_dec_ref_known(v_a_1317_, 2);
v___x_1326_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1304_, v_id_1325_);
lean_dec(v_id_1325_);
if (v___x_1326_ == 0)
{
lean_dec_ref_known(v___x_1306_, 3);
lean_dec(v_stx_1289_);
return v___x_1322_;
}
else
{
lean_object* v___x_1327_; 
lean_dec_ref(v___x_1322_);
v___x_1327_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v___x_1306_, v_a_1295_);
lean_dec_ref_known(v___x_1306_, 3);
return v___x_1327_;
}
}
}
else
{
lean_dec(v_a_1317_);
lean_dec_ref_known(v___x_1306_, 3);
lean_dec(v_stx_1289_);
return v___x_1322_;
}
}
else
{
lean_dec(v_a_1317_);
lean_dec_ref_known(v___x_1306_, 3);
lean_dec(v_stx_1289_);
return v___x_1322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_stx_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
return v_res_1338_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_1344_ = l_Lean_mkConst(v___x_1343_, v___x_1342_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1345_; lean_object* v_ty_x3f_1346_; 
v___x_1345_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_1346_, 0, v___x_1345_);
return v_ty_x3f_1346_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_1348_ = l_Lean_MessageData_ofExpr(v___x_1347_);
return v___x_1348_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_1350_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___x_1349_);
return v___x_1351_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1353_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_ty_x3f_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_toCold_1369_; lean_object* v_currRecDepth_1370_; lean_object* v_ref_1371_; uint16_t v_optionFlags_1372_; uint8_t v_suppressElabErrors_1373_; uint8_t v_checkDeprecated_1374_; uint8_t v_isRecordingDeps_1375_; uint8_t v___x_1376_; lean_object* v_ref_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_ty_x3f_1363_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_1364_ = 1;
v___x_1365_ = lean_box(0);
v___x_1366_ = lean_box(v___x_1364_);
v___x_1367_ = lean_box(v___x_1364_);
lean_inc(v_stx_1355_);
v___x_1368_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1368_, 0, v_stx_1355_);
lean_closure_set(v___x_1368_, 1, v_ty_x3f_1363_);
lean_closure_set(v___x_1368_, 2, v___x_1366_);
lean_closure_set(v___x_1368_, 3, v___x_1367_);
lean_closure_set(v___x_1368_, 4, v___x_1365_);
v_toCold_1369_ = lean_ctor_get(v_a_1360_, 0);
v_currRecDepth_1370_ = lean_ctor_get(v_a_1360_, 1);
v_ref_1371_ = lean_ctor_get(v_a_1360_, 2);
v_optionFlags_1372_ = lean_ctor_get_uint16(v_a_1360_, sizeof(void*)*3);
v_suppressElabErrors_1373_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*3 + 2);
v_checkDeprecated_1374_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1375_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*3 + 4);
v___x_1376_ = 1;
v_ref_1377_ = l_Lean_replaceRef(v_stx_1355_, v_ref_1371_);
lean_dec(v_stx_1355_);
lean_inc(v_currRecDepth_1370_);
lean_inc_ref(v_toCold_1369_);
v___x_1378_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1378_, 0, v_toCold_1369_);
lean_ctor_set(v___x_1378_, 1, v_currRecDepth_1370_);
lean_ctor_set(v___x_1378_, 2, v_ref_1377_);
lean_ctor_set_uint16(v___x_1378_, sizeof(void*)*3, v_optionFlags_1372_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*3 + 2, v_suppressElabErrors_1373_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*3 + 3, v_checkDeprecated_1374_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*3 + 4, v_isRecordingDeps_1375_);
v___x_1379_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1368_, v___x_1376_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v___x_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; lean_object* v_a_1382_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___x_1466_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1380_, v_a_1359_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref(v___x_1381_);
v___x_1466_ = l_Lean_Expr_hasSorry(v_a_1382_);
if (v___x_1466_ == 0)
{
v___y_1411_ = v_a_1356_;
v___y_1412_ = v_a_1357_;
v___y_1413_ = v_a_1358_;
v___y_1414_ = v_a_1359_;
v___y_1415_ = v___x_1378_;
v___y_1416_ = v_a_1361_;
goto v___jp_1410_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Lean_Expr_hasSyntheticSorry(v_a_1382_);
if (v___x_1467_ == 0)
{
v___y_1448_ = v_a_1356_;
v___y_1449_ = v_a_1357_;
v___y_1450_ = v_a_1358_;
v___y_1451_ = v_a_1359_;
v___y_1452_ = v___x_1378_;
v___y_1453_ = v_a_1361_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1468_; lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_a_1382_);
lean_dec_ref_known(v___x_1378_, 3);
v___x_1468_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
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
v___jp_1383_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1382_);
v___x_1391_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_a_1382_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_dec_ref(v___y_1388_);
lean_dec(v_a_1382_);
return v___x_1391_;
}
else
{
lean_object* v_a_1392_; uint8_t v___x_1393_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
v___x_1393_ = l_Lean_Exception_isInterrupt(v_a_1392_);
if (v___x_1393_ == 0)
{
uint8_t v___x_1394_; 
lean_inc(v_a_1392_);
v___x_1394_ = l_Lean_Exception_isRuntime(v_a_1392_);
if (v___x_1394_ == 0)
{
if (lean_obj_tag(v_a_1392_) == 0)
{
lean_dec_ref_known(v_a_1392_, 2);
lean_dec_ref(v___y_1388_);
lean_dec(v_a_1382_);
return v___x_1391_;
}
else
{
lean_object* v_id_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1408_; 
v_id_1395_ = lean_ctor_get(v_a_1392_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_a_1392_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_a_1392_, 1);
lean_dec(v_unused_1409_);
v___x_1397_ = v_a_1392_;
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_id_1395_);
lean_dec(v_a_1392_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
uint8_t v___x_1399_; 
v___x_1399_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1390_, v_id_1395_);
lean_dec(v_id_1395_);
if (v___x_1399_ == 0)
{
lean_del_object(v___x_1397_);
lean_dec_ref(v___y_1388_);
lean_dec(v_a_1382_);
return v___x_1391_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec_ref_known(v___x_1391_, 1);
v___x_1400_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_1401_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1402_ = l_Lean_indentExpr(v_a_1382_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 7);
lean_ctor_set(v___x_1397_, 1, v___x_1402_);
lean_ctor_set(v___x_1397_, 0, v___x_1401_);
v___x_1404_ = v___x_1397_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v___x_1400_);
v___x_1406_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1405_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v___y_1388_);
return v___x_1406_;
}
}
}
}
}
else
{
lean_dec(v_a_1392_);
lean_dec_ref(v___y_1388_);
lean_dec(v_a_1382_);
return v___x_1391_;
}
}
else
{
lean_dec(v_a_1392_);
lean_dec_ref(v___y_1388_);
lean_dec(v_a_1382_);
return v___x_1391_;
}
}
}
v___jp_1410_:
{
lean_object* v___x_1417_; 
lean_inc(v_a_1382_);
v___x_1417_ = l_Lean_Meta_getMVars(v_a_1382_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1418_, v___x_1365_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v_a_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; uint8_t v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = lean_unbox(v_a_1420_);
lean_dec(v_a_1420_);
if (v___x_1421_ == 0)
{
v___y_1384_ = v___y_1411_;
v___y_1385_ = v___y_1412_;
v___y_1386_ = v___y_1413_;
v___y_1387_ = v___y_1414_;
v___y_1388_ = v___y_1415_;
v___y_1389_ = v___y_1416_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1422_; lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v___y_1415_);
lean_dec(v_a_1382_);
v___x_1422_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v___y_1415_);
lean_dec(v_a_1382_);
v_a_1431_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1419_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1419_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v___y_1415_);
lean_dec(v_a_1382_);
v_a_1439_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1417_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1417_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
v___jp_1447_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v___x_1454_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1455_ = l_Lean_indentExpr(v_a_1382_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1456_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec_ref(v___y_1452_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
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
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref_known(v___x_1378_, 3);
v_a_1477_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1379_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1379_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_toCold_1502_; lean_object* v_currRecDepth_1503_; lean_object* v_ref_1504_; uint16_t v_optionFlags_1505_; uint8_t v_suppressElabErrors_1506_; uint8_t v_checkDeprecated_1507_; uint8_t v_isRecordingDeps_1508_; lean_object* v___x_1509_; lean_object* v_ref_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_toCold_1502_ = lean_ctor_get(v_a_1499_, 0);
v_currRecDepth_1503_ = lean_ctor_get(v_a_1499_, 1);
v_ref_1504_ = lean_ctor_get(v_a_1499_, 2);
v_optionFlags_1505_ = lean_ctor_get_uint16(v_a_1499_, sizeof(void*)*3);
v_suppressElabErrors_1506_ = lean_ctor_get_uint8(v_a_1499_, sizeof(void*)*3 + 2);
v_checkDeprecated_1507_ = lean_ctor_get_uint8(v_a_1499_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1508_ = lean_ctor_get_uint8(v_a_1499_, sizeof(void*)*3 + 4);
v___x_1509_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1510_ = l_Lean_replaceRef(v_stx_1494_, v_ref_1504_);
lean_inc(v_currRecDepth_1503_);
lean_inc_ref(v_toCold_1502_);
v___x_1511_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1511_, 0, v_toCold_1502_);
lean_ctor_set(v___x_1511_, 1, v_currRecDepth_1503_);
lean_ctor_set(v___x_1511_, 2, v_ref_1510_);
lean_ctor_set_uint16(v___x_1511_, sizeof(void*)*3, v_optionFlags_1505_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*3 + 2, v_suppressElabErrors_1506_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*3 + 3, v_checkDeprecated_1507_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*3 + 4, v_isRecordingDeps_1508_);
lean_inc(v_stx_1494_);
v___x_1512_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v___x_1511_, v_a_1500_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref_known(v___x_1511_, 3);
lean_dec(v_stx_1494_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_fst_1517_; lean_object* v___x_1519_; 
v_fst_1517_ = lean_ctor_get(v_a_1513_, 0);
lean_inc(v_fst_1517_);
lean_dec(v_a_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_fst_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_fst_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1534_; 
v_a_1522_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1524_ = v___x_1512_;
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1512_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1534_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
lean_inc(v_a_1522_);
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
uint8_t v___x_1528_; 
v___x_1528_ = l_Lean_Exception_isInterrupt(v_a_1522_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; 
lean_inc(v_a_1522_);
v___x_1529_ = l_Lean_Exception_isRuntime(v_a_1522_);
if (v___x_1529_ == 0)
{
if (lean_obj_tag(v_a_1522_) == 0)
{
lean_dec_ref_known(v_a_1522_, 2);
lean_dec_ref_known(v___x_1511_, 3);
lean_dec(v_stx_1494_);
return v___x_1527_;
}
else
{
lean_object* v_id_1530_; uint8_t v___x_1531_; 
v_id_1530_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_id_1530_);
lean_dec_ref_known(v_a_1522_, 2);
v___x_1531_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1509_, v_id_1530_);
lean_dec(v_id_1530_);
if (v___x_1531_ == 0)
{
lean_dec_ref_known(v___x_1511_, 3);
lean_dec(v_stx_1494_);
return v___x_1527_;
}
else
{
lean_object* v___x_1532_; 
lean_dec_ref(v___x_1527_);
v___x_1532_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v___x_1511_, v_a_1500_);
lean_dec_ref_known(v___x_1511_, 3);
return v___x_1532_;
}
}
}
else
{
lean_dec(v_a_1522_);
lean_dec_ref_known(v___x_1511_, 3);
lean_dec(v_stx_1494_);
return v___x_1527_;
}
}
else
{
lean_dec(v_a_1522_);
lean_dec_ref_known(v___x_1511_, 3);
lean_dec(v_stx_1494_);
return v___x_1527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_stx_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(lean_object* v_config_1666_, lean_object* v_item_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_item_1676_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_1680_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1667_, v___x_1679_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1680_) == 0)
{
uint8_t v___x_1681_; 
lean_dec_ref_known(v___x_1680_, 1);
v___x_1681_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1667_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1682_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1667_);
lean_inc_ref(v_item_1667_);
v___x_1683_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1667_);
v___x_1684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_1685_ = lean_string_dec_lt(v___x_1682_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_1687_ = lean_string_dec_lt(v___x_1682_, v___x_1686_);
if (v___x_1687_ == 0)
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_string_dec_eq(v___x_1682_, v___x_1686_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_1690_ = lean_string_dec_eq(v___x_1682_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_1692_ = lean_string_dec_eq(v___x_1682_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_));
v___x_1694_ = lean_string_dec_eq(v___x_1682_, v___x_1693_);
lean_dec_ref(v___x_1682_);
if (v___x_1694_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_1696_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_1695_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1696_) == 0)
{
uint8_t v___x_1697_; 
lean_dec_ref_known(v___x_1696_, 1);
v___x_1697_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_1697_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1698_; 
lean_dec_ref(v___x_1683_);
v___x_1698_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1728_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1728_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1728_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_timeout_1703_; uint8_t v_trimProofs_1704_; uint8_t v_binaryProofs_1705_; uint8_t v_acNf_1706_; uint8_t v_andFlattening_1707_; uint8_t v_embeddedConstraintSubst_1708_; uint8_t v_structures_1709_; uint8_t v_fixedInt_1710_; uint8_t v_enums_1711_; uint8_t v_graphviz_1712_; lean_object* v_maxSteps_1713_; uint8_t v_shortCircuit_1714_; uint8_t v_solverMode_1715_; lean_object* v_cegarRounds_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1727_; 
v_timeout_1703_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_1704_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_1705_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_1706_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_1707_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1708_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_1709_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_1710_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_1711_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_1712_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_1713_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_1714_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_1715_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_cegarRounds_1716_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1718_ = v_config_1666_;
v_isShared_1719_ = v_isSharedCheck_1727_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_cegarRounds_1716_);
lean_inc(v_maxSteps_1713_);
lean_inc(v_timeout_1703_);
lean_dec(v_config_1666_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1727_;
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
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_timeout_1703_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_maxSteps_1713_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_cegarRounds_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3, v_trimProofs_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 1, v_binaryProofs_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 2, v_acNf_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 3, v_andFlattening_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1708_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 5, v_structures_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 6, v_fixedInt_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 7, v_enums_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 8, v_graphviz_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 9, v_shortCircuit_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1726_, sizeof(void*)*3 + 10, v_solverMode_1715_);
v___x_1721_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
uint8_t v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_unbox(v_a_1699_);
lean_dec(v_a_1699_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*3 + 11, v___x_1722_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1721_);
v___x_1724_ = v___x_1701_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1721_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_config_1666_);
v_a_1729_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1698_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1698_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_1737_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1696_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1696_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
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
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec_ref(v___x_1682_);
v___x_1745_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_1746_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_1745_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1746_) == 0)
{
uint8_t v___x_1747_; 
lean_dec_ref_known(v___x_1746_, 1);
v___x_1747_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_1747_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1748_; 
lean_dec_ref(v___x_1683_);
v___x_1748_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1778_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1778_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1778_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_timeout_1753_; uint8_t v_binaryProofs_1754_; uint8_t v_acNf_1755_; uint8_t v_andFlattening_1756_; uint8_t v_embeddedConstraintSubst_1757_; uint8_t v_structures_1758_; uint8_t v_fixedInt_1759_; uint8_t v_enums_1760_; uint8_t v_graphviz_1761_; lean_object* v_maxSteps_1762_; uint8_t v_shortCircuit_1763_; uint8_t v_solverMode_1764_; uint8_t v_uf_1765_; lean_object* v_cegarRounds_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1777_; 
v_timeout_1753_ = lean_ctor_get(v_config_1666_, 0);
v_binaryProofs_1754_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_1755_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_1756_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1757_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_1758_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_1759_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_1760_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_1761_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_1762_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_1763_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_1764_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_1765_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_1766_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1768_ = v_config_1666_;
v_isShared_1769_ = v_isSharedCheck_1777_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_cegarRounds_1766_);
lean_inc(v_maxSteps_1762_);
lean_inc(v_timeout_1753_);
lean_dec(v_config_1666_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1777_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_timeout_1753_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_maxSteps_1762_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_cegarRounds_1766_);
v___x_1771_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
uint8_t v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_unbox(v_a_1749_);
lean_dec(v_a_1749_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3, v___x_1772_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 1, v_binaryProofs_1754_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 2, v_acNf_1755_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 3, v_andFlattening_1756_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1757_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 5, v_structures_1758_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 6, v_fixedInt_1759_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 7, v_enums_1760_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 8, v_graphviz_1761_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 9, v_shortCircuit_1763_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 10, v_solverMode_1764_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*3 + 11, v_uf_1765_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1771_);
v___x_1774_ = v___x_1751_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1771_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v_config_1666_);
v_a_1779_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1748_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1748_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_1787_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1746_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1746_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec_ref(v___x_1682_);
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_1796_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_1795_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1796_) == 0)
{
uint8_t v___x_1797_; 
lean_dec_ref_known(v___x_1796_, 1);
v___x_1797_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref(v___x_1683_);
lean_inc_ref(v_item_1667_);
v___x_1798_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_value_1799_; lean_object* v___x_1800_; 
lean_dec_ref_known(v___x_1798_, 1);
v_value_1799_ = lean_ctor_get(v_item_1667_, 2);
lean_inc(v_value_1799_);
lean_dec_ref(v_item_1667_);
v___x_1800_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1799_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1830_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1830_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1830_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint8_t v_trimProofs_1805_; uint8_t v_binaryProofs_1806_; uint8_t v_acNf_1807_; uint8_t v_andFlattening_1808_; uint8_t v_embeddedConstraintSubst_1809_; uint8_t v_structures_1810_; uint8_t v_fixedInt_1811_; uint8_t v_enums_1812_; uint8_t v_graphviz_1813_; lean_object* v_maxSteps_1814_; uint8_t v_shortCircuit_1815_; uint8_t v_solverMode_1816_; uint8_t v_uf_1817_; lean_object* v_cegarRounds_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v_trimProofs_1805_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_1806_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_1807_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_1808_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1809_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_1810_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_1811_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_1812_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_1813_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_1814_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_1815_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_1816_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_1817_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_1818_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_config_1666_, 0);
lean_dec(v_unused_1829_);
v___x_1820_ = v_config_1666_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_cegarRounds_1818_);
lean_inc(v_maxSteps_1814_);
lean_dec(v_config_1666_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v_a_1801_);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1801_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_maxSteps_1814_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_cegarRounds_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3, v_trimProofs_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 1, v_binaryProofs_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 2, v_acNf_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 3, v_andFlattening_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 5, v_structures_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 6, v_fixedInt_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 7, v_enums_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 8, v_graphviz_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 9, v_shortCircuit_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 10, v_solverMode_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*3 + 11, v_uf_1817_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1823_);
v___x_1825_ = v___x_1803_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v_config_1666_);
v_a_1831_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1800_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1800_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_1839_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1798_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1798_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
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
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_1847_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1796_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1796_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v___x_1682_);
v___x_1855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_1856_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_1855_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1856_) == 0)
{
uint8_t v___x_1857_; 
lean_dec_ref_known(v___x_1856_, 1);
v___x_1857_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1858_; 
lean_dec_ref(v___x_1683_);
v___x_1858_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1888_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1888_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1888_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v_timeout_1863_; uint8_t v_trimProofs_1864_; uint8_t v_binaryProofs_1865_; uint8_t v_acNf_1866_; uint8_t v_andFlattening_1867_; uint8_t v_embeddedConstraintSubst_1868_; uint8_t v_fixedInt_1869_; uint8_t v_enums_1870_; uint8_t v_graphviz_1871_; lean_object* v_maxSteps_1872_; uint8_t v_shortCircuit_1873_; uint8_t v_solverMode_1874_; uint8_t v_uf_1875_; lean_object* v_cegarRounds_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1887_; 
v_timeout_1863_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_1864_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_1865_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_1866_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_1867_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1868_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_fixedInt_1869_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_1870_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_1871_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_1872_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_1873_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_1874_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_1875_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_1876_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1878_ = v_config_1666_;
v_isShared_1879_ = v_isSharedCheck_1887_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_cegarRounds_1876_);
lean_inc(v_maxSteps_1872_);
lean_inc(v_timeout_1863_);
lean_dec(v_config_1666_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1887_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_timeout_1863_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_maxSteps_1872_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_cegarRounds_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*3, v_trimProofs_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*3 + 1, v_binaryProofs_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*3 + 2, v_acNf_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*3 + 3, v_andFlattening_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1868_);
v___x_1881_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
uint8_t v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_unbox(v_a_1859_);
lean_dec(v_a_1859_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*3 + 5, v___x_1882_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*3 + 6, v_fixedInt_1869_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*3 + 7, v_enums_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*3 + 8, v_graphviz_1871_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*3 + 9, v_shortCircuit_1873_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*3 + 10, v_solverMode_1874_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*3 + 11, v_uf_1875_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1881_);
v___x_1884_ = v___x_1861_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1881_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v_config_1666_);
v_a_1889_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1858_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1858_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_1897_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1856_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1856_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_string_dec_eq(v___x_1682_, v___x_1684_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_1907_ = lean_string_dec_eq(v___x_1682_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10));
v___x_1909_ = lean_string_dec_eq(v___x_1682_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11));
v___x_1911_ = lean_string_dec_eq(v___x_1682_, v___x_1910_);
lean_dec_ref(v___x_1682_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12));
v___x_1913_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_1912_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1913_) == 0)
{
uint8_t v___x_1914_; 
lean_dec_ref_known(v___x_1913_, 1);
v___x_1914_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_1914_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1915_; 
lean_dec_ref(v___x_1683_);
lean_inc_ref(v_item_1667_);
v___x_1915_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_value_1916_; lean_object* v___x_1917_; 
lean_dec_ref_known(v___x_1915_, 1);
v_value_1916_ = lean_ctor_get(v_item_1667_, 2);
lean_inc(v_value_1916_);
lean_dec_ref(v_item_1667_);
v___x_1917_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_value_1916_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1947_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1947_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1947_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_timeout_1922_; uint8_t v_trimProofs_1923_; uint8_t v_binaryProofs_1924_; uint8_t v_acNf_1925_; uint8_t v_andFlattening_1926_; uint8_t v_embeddedConstraintSubst_1927_; uint8_t v_structures_1928_; uint8_t v_fixedInt_1929_; uint8_t v_enums_1930_; uint8_t v_graphviz_1931_; lean_object* v_maxSteps_1932_; uint8_t v_shortCircuit_1933_; uint8_t v_uf_1934_; lean_object* v_cegarRounds_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1946_; 
v_timeout_1922_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_1923_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_1924_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_1925_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_1926_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1927_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_1928_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_1929_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_1930_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_1931_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_1932_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_1933_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_uf_1934_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_1935_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1937_ = v_config_1666_;
v_isShared_1938_ = v_isSharedCheck_1946_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_cegarRounds_1935_);
lean_inc(v_maxSteps_1932_);
lean_inc(v_timeout_1922_);
lean_dec(v_config_1666_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1946_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_timeout_1922_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_maxSteps_1932_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_cegarRounds_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3, v_trimProofs_1923_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 1, v_binaryProofs_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 2, v_acNf_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 3, v_andFlattening_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 5, v_structures_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 6, v_fixedInt_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 7, v_enums_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 8, v_graphviz_1931_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 9, v_shortCircuit_1933_);
v___x_1940_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
uint8_t v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3 + 10, v___x_1941_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3 + 11, v_uf_1934_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1940_);
v___x_1943_ = v___x_1920_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1940_);
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
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_config_1666_);
v_a_1948_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1917_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1917_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_1956_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1915_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1915_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_1964_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1913_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1913_);
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
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec_ref(v___x_1682_);
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13));
v___x_1973_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_1972_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1973_) == 0)
{
uint8_t v___x_1974_; 
lean_dec_ref_known(v___x_1973_, 1);
v___x_1974_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_1974_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1975_; 
lean_dec_ref(v___x_1683_);
v___x_1975_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2005_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_2005_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2005_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_timeout_1980_; uint8_t v_trimProofs_1981_; uint8_t v_binaryProofs_1982_; uint8_t v_acNf_1983_; uint8_t v_andFlattening_1984_; uint8_t v_embeddedConstraintSubst_1985_; uint8_t v_structures_1986_; uint8_t v_fixedInt_1987_; uint8_t v_enums_1988_; uint8_t v_graphviz_1989_; lean_object* v_maxSteps_1990_; uint8_t v_solverMode_1991_; uint8_t v_uf_1992_; lean_object* v_cegarRounds_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2004_; 
v_timeout_1980_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_1981_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_1982_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_1983_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_1984_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1985_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_1986_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_1987_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_1988_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_1989_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_1990_ = lean_ctor_get(v_config_1666_, 1);
v_solverMode_1991_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_1992_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_1993_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1995_ = v_config_1666_;
v_isShared_1996_ = v_isSharedCheck_2004_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_cegarRounds_1993_);
lean_inc(v_maxSteps_1990_);
lean_inc(v_timeout_1980_);
lean_dec(v_config_1666_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2004_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_timeout_1980_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_maxSteps_1990_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_cegarRounds_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3, v_trimProofs_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 1, v_binaryProofs_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 2, v_acNf_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 3, v_andFlattening_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 5, v_structures_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 6, v_fixedInt_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 7, v_enums_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*3 + 8, v_graphviz_1989_);
v___x_1998_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
uint8_t v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_unbox(v_a_1976_);
lean_dec(v_a_1976_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*3 + 9, v___x_1999_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*3 + 10, v_solverMode_1991_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*3 + 11, v_uf_1992_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1998_);
v___x_2001_ = v___x_1978_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1998_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref(v_config_1666_);
v_a_2006_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1975_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1975_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2014_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1973_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1973_);
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
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref(v___x_1682_);
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14));
v___x_2023_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2022_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2023_) == 0)
{
uint8_t v___x_2024_; 
lean_dec_ref_known(v___x_2023_, 1);
v___x_2024_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2024_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2025_; 
lean_dec_ref(v___x_1683_);
lean_inc_ref(v_item_1667_);
v___x_2025_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_value_2026_; lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_2025_, 1);
v_value_2026_ = lean_ctor_get(v_item_1667_, 2);
lean_inc(v_value_2026_);
lean_dec_ref(v_item_1667_);
v___x_2027_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_2026_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2057_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_timeout_2032_; uint8_t v_trimProofs_2033_; uint8_t v_binaryProofs_2034_; uint8_t v_acNf_2035_; uint8_t v_andFlattening_2036_; uint8_t v_embeddedConstraintSubst_2037_; uint8_t v_structures_2038_; uint8_t v_fixedInt_2039_; uint8_t v_enums_2040_; uint8_t v_graphviz_2041_; uint8_t v_shortCircuit_2042_; uint8_t v_solverMode_2043_; uint8_t v_uf_2044_; lean_object* v_cegarRounds_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2055_; 
v_timeout_2032_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2033_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2034_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_2035_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_2036_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2037_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2038_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2039_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_2040_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_2041_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_shortCircuit_2042_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2043_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2044_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2045_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v_config_1666_, 1);
lean_dec(v_unused_2056_);
v___x_2047_ = v_config_1666_;
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_cegarRounds_2045_);
lean_inc(v_timeout_2032_);
lean_dec(v_config_1666_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v_a_2028_);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_timeout_2032_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_a_2028_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_cegarRounds_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3, v_trimProofs_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 1, v_binaryProofs_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 2, v_acNf_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 3, v_andFlattening_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 5, v_structures_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 6, v_fixedInt_2039_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 7, v_enums_2040_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 8, v_graphviz_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 9, v_shortCircuit_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 10, v_solverMode_2043_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*3 + 11, v_uf_2044_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2050_);
v___x_2052_ = v___x_2030_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_config_1666_);
v_a_2058_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2027_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2027_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2066_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2025_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2025_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2074_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2023_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2023_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v___x_1682_);
v___x_2082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15));
v___x_2083_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2082_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2083_) == 0)
{
uint8_t v___x_2084_; 
lean_dec_ref_known(v___x_2083_, 1);
v___x_2084_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2085_; 
lean_dec_ref(v___x_1683_);
v___x_2085_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2115_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2115_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2115_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_timeout_2090_; uint8_t v_trimProofs_2091_; uint8_t v_binaryProofs_2092_; uint8_t v_acNf_2093_; uint8_t v_andFlattening_2094_; uint8_t v_embeddedConstraintSubst_2095_; uint8_t v_structures_2096_; uint8_t v_fixedInt_2097_; uint8_t v_enums_2098_; lean_object* v_maxSteps_2099_; uint8_t v_shortCircuit_2100_; uint8_t v_solverMode_2101_; uint8_t v_uf_2102_; lean_object* v_cegarRounds_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2114_; 
v_timeout_2090_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2091_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2092_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_2093_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_2094_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2095_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2096_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2097_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_2098_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_maxSteps_2099_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2100_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2101_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2102_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2103_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2105_ = v_config_1666_;
v_isShared_2106_ = v_isSharedCheck_2114_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_cegarRounds_2103_);
lean_inc(v_maxSteps_2099_);
lean_inc(v_timeout_2090_);
lean_dec(v_config_1666_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2114_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_timeout_2090_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_maxSteps_2099_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_cegarRounds_2103_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3, v_trimProofs_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3 + 1, v_binaryProofs_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3 + 2, v_acNf_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3 + 3, v_andFlattening_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3 + 5, v_structures_2096_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3 + 6, v_fixedInt_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*3 + 7, v_enums_2098_);
v___x_2108_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
uint8_t v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_unbox(v_a_2086_);
lean_dec(v_a_2086_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*3 + 8, v___x_2109_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*3 + 9, v_shortCircuit_2100_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*3 + 10, v_solverMode_2101_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*3 + 11, v_uf_2102_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2108_);
v___x_2111_ = v___x_2088_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2108_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v_config_1666_);
v_a_2116_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2085_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2085_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2124_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2083_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2083_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
else
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16));
v___x_2133_ = lean_string_dec_lt(v___x_1682_, v___x_2132_);
if (v___x_2133_ == 0)
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_string_dec_eq(v___x_1682_, v___x_2132_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17));
v___x_2136_ = lean_string_dec_eq(v___x_1682_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18));
v___x_2138_ = lean_string_dec_eq(v___x_1682_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19));
v___x_2140_ = lean_string_dec_eq(v___x_1682_, v___x_2139_);
lean_dec_ref(v___x_1682_);
if (v___x_2140_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20));
v___x_2142_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2141_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2142_) == 0)
{
uint8_t v___x_2143_; 
lean_dec_ref_known(v___x_2142_, 1);
v___x_2143_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2143_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2144_; 
lean_dec_ref(v___x_1683_);
v___x_2144_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2174_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2174_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2174_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v_timeout_2149_; uint8_t v_trimProofs_2150_; uint8_t v_binaryProofs_2151_; uint8_t v_acNf_2152_; uint8_t v_andFlattening_2153_; uint8_t v_embeddedConstraintSubst_2154_; uint8_t v_structures_2155_; uint8_t v_enums_2156_; uint8_t v_graphviz_2157_; lean_object* v_maxSteps_2158_; uint8_t v_shortCircuit_2159_; uint8_t v_solverMode_2160_; uint8_t v_uf_2161_; lean_object* v_cegarRounds_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2173_; 
v_timeout_2149_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2150_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2151_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_2152_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_2153_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2154_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2155_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_enums_2156_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_2157_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_2158_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2159_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2160_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2161_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2162_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2164_ = v_config_1666_;
v_isShared_2165_ = v_isSharedCheck_2173_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_cegarRounds_2162_);
lean_inc(v_maxSteps_2158_);
lean_inc(v_timeout_2149_);
lean_dec(v_config_1666_);
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
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_timeout_2149_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_maxSteps_2158_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_cegarRounds_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3, v_trimProofs_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3 + 1, v_binaryProofs_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3 + 2, v_acNf_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3 + 3, v_andFlattening_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3 + 5, v_structures_2155_);
v___x_2167_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
uint8_t v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_unbox(v_a_2145_);
lean_dec(v_a_2145_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*3 + 6, v___x_2168_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*3 + 7, v_enums_2156_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*3 + 8, v_graphviz_2157_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*3 + 9, v_shortCircuit_2159_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*3 + 10, v_solverMode_2160_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*3 + 11, v_uf_2161_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2167_);
v___x_2170_ = v___x_2147_;
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
lean_dec_ref(v_config_1666_);
v_a_2175_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2144_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2144_);
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
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2183_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2142_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2142_);
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
lean_dec_ref(v___x_1682_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21));
v___x_2192_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2191_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2192_) == 0)
{
uint8_t v___x_2193_; 
lean_dec_ref_known(v___x_2192_, 1);
v___x_2193_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2193_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2194_; 
lean_dec_ref(v___x_1683_);
v___x_2194_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2224_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2224_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2224_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v_timeout_2199_; uint8_t v_trimProofs_2200_; uint8_t v_binaryProofs_2201_; uint8_t v_acNf_2202_; uint8_t v_andFlattening_2203_; uint8_t v_embeddedConstraintSubst_2204_; uint8_t v_structures_2205_; uint8_t v_fixedInt_2206_; uint8_t v_graphviz_2207_; lean_object* v_maxSteps_2208_; uint8_t v_shortCircuit_2209_; uint8_t v_solverMode_2210_; uint8_t v_uf_2211_; lean_object* v_cegarRounds_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2223_; 
v_timeout_2199_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2200_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2201_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_2202_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_2203_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2204_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2205_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2206_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_graphviz_2207_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_2208_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2209_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2210_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2211_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2212_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2214_ = v_config_1666_;
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_cegarRounds_2212_);
lean_inc(v_maxSteps_2208_);
lean_inc(v_timeout_2199_);
lean_dec(v_config_1666_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_timeout_2199_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_maxSteps_2208_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_cegarRounds_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3, v_trimProofs_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 1, v_binaryProofs_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 2, v_acNf_2202_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 3, v_andFlattening_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 5, v_structures_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*3 + 6, v_fixedInt_2206_);
v___x_2217_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
uint8_t v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_unbox(v_a_2195_);
lean_dec(v_a_2195_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*3 + 7, v___x_2218_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*3 + 8, v_graphviz_2207_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*3 + 9, v_shortCircuit_2209_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*3 + 10, v_solverMode_2210_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*3 + 11, v_uf_2211_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2217_);
v___x_2220_ = v___x_2197_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2217_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_config_1666_);
v_a_2225_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2194_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2194_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2233_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2192_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2192_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v___x_1682_);
v___x_2241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22));
v___x_2242_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2241_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2242_) == 0)
{
uint8_t v___x_2243_; 
lean_dec_ref_known(v___x_2242_, 1);
v___x_2243_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2243_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2244_; 
lean_dec_ref(v___x_1683_);
v___x_2244_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2274_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2274_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2274_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_timeout_2249_; uint8_t v_trimProofs_2250_; uint8_t v_binaryProofs_2251_; uint8_t v_acNf_2252_; uint8_t v_andFlattening_2253_; uint8_t v_structures_2254_; uint8_t v_fixedInt_2255_; uint8_t v_enums_2256_; uint8_t v_graphviz_2257_; lean_object* v_maxSteps_2258_; uint8_t v_shortCircuit_2259_; uint8_t v_solverMode_2260_; uint8_t v_uf_2261_; lean_object* v_cegarRounds_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2273_; 
v_timeout_2249_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2250_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2251_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_2252_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_2253_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_structures_2254_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2255_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_2256_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_2257_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_2258_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2259_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2260_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2261_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2262_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2264_ = v_config_1666_;
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_cegarRounds_2262_);
lean_inc(v_maxSteps_2258_);
lean_inc(v_timeout_2249_);
lean_dec(v_config_1666_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2273_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_timeout_2249_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_maxSteps_2258_);
lean_ctor_set(v_reuseFailAlloc_2272_, 2, v_cegarRounds_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2272_, sizeof(void*)*3, v_trimProofs_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2272_, sizeof(void*)*3 + 1, v_binaryProofs_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2272_, sizeof(void*)*3 + 2, v_acNf_2252_);
lean_ctor_set_uint8(v_reuseFailAlloc_2272_, sizeof(void*)*3 + 3, v_andFlattening_2253_);
v___x_2267_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
uint8_t v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_unbox(v_a_2245_);
lean_dec(v_a_2245_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 4, v___x_2268_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 5, v_structures_2254_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 6, v_fixedInt_2255_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 7, v_enums_2256_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 8, v_graphviz_2257_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 9, v_shortCircuit_2259_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 10, v_solverMode_2260_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 11, v_uf_2261_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2267_);
v___x_2270_ = v___x_2247_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2267_);
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
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v_config_1666_);
v_a_2275_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2244_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2244_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2283_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2242_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2242_);
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
else
{
uint8_t v___x_2291_; 
lean_dec_ref(v___x_1682_);
lean_dec_ref(v_config_1666_);
v___x_2291_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2291_ == 0)
{
lean_dec_ref(v_item_1667_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v_value_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v___x_1683_);
v_value_2292_ = lean_ctor_get(v_item_1667_, 2);
lean_inc(v_value_2292_);
lean_dec_ref(v_item_1667_);
v___x_2293_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_value_2292_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_2293_;
}
}
}
else
{
lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23));
v___x_2295_ = lean_string_dec_eq(v___x_1682_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24));
v___x_2297_ = lean_string_dec_eq(v___x_1682_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25));
v___x_2299_ = lean_string_dec_eq(v___x_1682_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26));
v___x_2301_ = lean_string_dec_eq(v___x_1682_, v___x_2300_);
lean_dec_ref(v___x_1682_);
if (v___x_2301_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27));
v___x_2303_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2302_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2303_) == 0)
{
uint8_t v___x_2304_; 
lean_dec_ref_known(v___x_2303_, 1);
v___x_2304_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2304_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2305_; 
lean_dec_ref(v___x_1683_);
lean_inc_ref(v_item_1667_);
v___x_2305_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_value_2306_; lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2305_, 1);
v_value_2306_ = lean_ctor_get(v_item_1667_, 2);
lean_inc(v_value_2306_);
lean_dec_ref(v_item_1667_);
v___x_2307_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_2306_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2337_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2337_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2337_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_timeout_2312_; uint8_t v_trimProofs_2313_; uint8_t v_binaryProofs_2314_; uint8_t v_acNf_2315_; uint8_t v_andFlattening_2316_; uint8_t v_embeddedConstraintSubst_2317_; uint8_t v_structures_2318_; uint8_t v_fixedInt_2319_; uint8_t v_enums_2320_; uint8_t v_graphviz_2321_; lean_object* v_maxSteps_2322_; uint8_t v_shortCircuit_2323_; uint8_t v_solverMode_2324_; uint8_t v_uf_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2335_; 
v_timeout_2312_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2313_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2314_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_2315_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_2316_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2317_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2318_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2319_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_2320_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_2321_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_2322_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2323_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2324_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2325_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v_config_1666_, 2);
lean_dec(v_unused_2336_);
v___x_2327_ = v_config_1666_;
v_isShared_2328_ = v_isSharedCheck_2335_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_maxSteps_2322_);
lean_inc(v_timeout_2312_);
lean_dec(v_config_1666_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2335_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 2, v_a_2308_);
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_timeout_2312_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_maxSteps_2322_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_a_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3, v_trimProofs_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 1, v_binaryProofs_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 2, v_acNf_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 3, v_andFlattening_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 5, v_structures_2318_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 6, v_fixedInt_2319_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 7, v_enums_2320_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 8, v_graphviz_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 9, v_shortCircuit_2323_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 10, v_solverMode_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2334_, sizeof(void*)*3 + 11, v_uf_2325_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2330_);
v___x_2332_ = v___x_2310_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_config_1666_);
v_a_2338_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2307_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2307_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2346_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2305_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2305_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2354_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2303_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2303_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec_ref(v___x_1682_);
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28));
v___x_2363_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2362_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2363_) == 0)
{
uint8_t v___x_2364_; 
lean_dec_ref_known(v___x_2363_, 1);
v___x_2364_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2364_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2365_; 
lean_dec_ref(v___x_1683_);
v___x_2365_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2395_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2395_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2395_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v_timeout_2370_; uint8_t v_trimProofs_2371_; uint8_t v_acNf_2372_; uint8_t v_andFlattening_2373_; uint8_t v_embeddedConstraintSubst_2374_; uint8_t v_structures_2375_; uint8_t v_fixedInt_2376_; uint8_t v_enums_2377_; uint8_t v_graphviz_2378_; lean_object* v_maxSteps_2379_; uint8_t v_shortCircuit_2380_; uint8_t v_solverMode_2381_; uint8_t v_uf_2382_; lean_object* v_cegarRounds_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2394_; 
v_timeout_2370_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2371_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_acNf_2372_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_andFlattening_2373_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2374_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2375_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2376_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_2377_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_2378_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_2379_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2380_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2381_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2382_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2383_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2385_ = v_config_1666_;
v_isShared_2386_ = v_isSharedCheck_2394_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_cegarRounds_2383_);
lean_inc(v_maxSteps_2379_);
lean_inc(v_timeout_2370_);
lean_dec(v_config_1666_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2394_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_timeout_2370_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_maxSteps_2379_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_cegarRounds_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*3, v_trimProofs_2371_);
v___x_2388_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
uint8_t v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_unbox(v_a_2366_);
lean_dec(v_a_2366_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 1, v___x_2389_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 2, v_acNf_2372_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 3, v_andFlattening_2373_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2374_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 5, v_structures_2375_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 6, v_fixedInt_2376_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 7, v_enums_2377_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 8, v_graphviz_2378_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 9, v_shortCircuit_2380_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 10, v_solverMode_2381_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*3 + 11, v_uf_2382_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2388_);
v___x_2391_ = v___x_2368_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2388_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec_ref(v_config_1666_);
v_a_2396_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2365_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2365_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2404_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2363_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2363_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v___x_1682_);
v___x_2412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29));
v___x_2413_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2412_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2413_) == 0)
{
uint8_t v___x_2414_; 
lean_dec_ref_known(v___x_2413_, 1);
v___x_2414_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2414_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2415_; 
lean_dec_ref(v___x_1683_);
v___x_2415_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2445_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2445_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2445_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_timeout_2420_; uint8_t v_trimProofs_2421_; uint8_t v_binaryProofs_2422_; uint8_t v_acNf_2423_; uint8_t v_embeddedConstraintSubst_2424_; uint8_t v_structures_2425_; uint8_t v_fixedInt_2426_; uint8_t v_enums_2427_; uint8_t v_graphviz_2428_; lean_object* v_maxSteps_2429_; uint8_t v_shortCircuit_2430_; uint8_t v_solverMode_2431_; uint8_t v_uf_2432_; lean_object* v_cegarRounds_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2444_; 
v_timeout_2420_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2421_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2422_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_acNf_2423_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 2);
v_embeddedConstraintSubst_2424_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2425_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2426_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_2427_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_2428_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_2429_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2430_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2431_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2432_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2433_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2435_ = v_config_1666_;
v_isShared_2436_ = v_isSharedCheck_2444_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_cegarRounds_2433_);
lean_inc(v_maxSteps_2429_);
lean_inc(v_timeout_2420_);
lean_dec(v_config_1666_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2444_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_timeout_2420_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_maxSteps_2429_);
lean_ctor_set(v_reuseFailAlloc_2443_, 2, v_cegarRounds_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2443_, sizeof(void*)*3, v_trimProofs_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2443_, sizeof(void*)*3 + 1, v_binaryProofs_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2443_, sizeof(void*)*3 + 2, v_acNf_2423_);
v___x_2438_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
uint8_t v___x_2439_; lean_object* v___x_2441_; 
v___x_2439_ = lean_unbox(v_a_2416_);
lean_dec(v_a_2416_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 3, v___x_2439_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2424_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 5, v_structures_2425_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 6, v_fixedInt_2426_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 7, v_enums_2427_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 8, v_graphviz_2428_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 9, v_shortCircuit_2430_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 10, v_solverMode_2431_);
lean_ctor_set_uint8(v___x_2438_, sizeof(void*)*3 + 11, v_uf_2432_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2438_);
v___x_2441_ = v___x_2418_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2438_);
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
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v_config_1666_);
v_a_2446_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2415_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2415_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2454_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2413_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2413_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec_ref(v___x_1682_);
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30));
v___x_2463_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1667_, v___x_2462_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2463_) == 0)
{
uint8_t v___x_2464_; 
lean_dec_ref_known(v___x_2463_, 1);
v___x_2464_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1683_);
if (v___x_2464_ == 0)
{
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_item_1676_ = v___x_1683_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_2465_; 
lean_dec_ref(v___x_1683_);
v___x_2465_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2495_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2495_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2495_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v_timeout_2470_; uint8_t v_trimProofs_2471_; uint8_t v_binaryProofs_2472_; uint8_t v_andFlattening_2473_; uint8_t v_embeddedConstraintSubst_2474_; uint8_t v_structures_2475_; uint8_t v_fixedInt_2476_; uint8_t v_enums_2477_; uint8_t v_graphviz_2478_; lean_object* v_maxSteps_2479_; uint8_t v_shortCircuit_2480_; uint8_t v_solverMode_2481_; uint8_t v_uf_2482_; lean_object* v_cegarRounds_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2494_; 
v_timeout_2470_ = lean_ctor_get(v_config_1666_, 0);
v_trimProofs_2471_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3);
v_binaryProofs_2472_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 1);
v_andFlattening_2473_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2474_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 4);
v_structures_2475_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 5);
v_fixedInt_2476_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 6);
v_enums_2477_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 7);
v_graphviz_2478_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 8);
v_maxSteps_2479_ = lean_ctor_get(v_config_1666_, 1);
v_shortCircuit_2480_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 9);
v_solverMode_2481_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 10);
v_uf_2482_ = lean_ctor_get_uint8(v_config_1666_, sizeof(void*)*3 + 11);
v_cegarRounds_2483_ = lean_ctor_get(v_config_1666_, 2);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_config_1666_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2485_ = v_config_1666_;
v_isShared_2486_ = v_isSharedCheck_2494_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_cegarRounds_2483_);
lean_inc(v_maxSteps_2479_);
lean_inc(v_timeout_2470_);
lean_dec(v_config_1666_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2494_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_timeout_2470_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_maxSteps_2479_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_cegarRounds_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2493_, sizeof(void*)*3, v_trimProofs_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2493_, sizeof(void*)*3 + 1, v_binaryProofs_2472_);
v___x_2488_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
uint8_t v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_unbox(v_a_2466_);
lean_dec(v_a_2466_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 2, v___x_2489_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 3, v_andFlattening_2473_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2474_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 5, v_structures_2475_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 6, v_fixedInt_2476_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 7, v_enums_2477_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 8, v_graphviz_2478_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 9, v_shortCircuit_2480_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 10, v_solverMode_2481_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*3 + 11, v_uf_2482_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2488_);
v___x_2491_ = v___x_2468_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2488_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v_config_1666_);
v_a_2496_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2465_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2465_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v___x_1683_);
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2504_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2463_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2463_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_config_1666_);
v_item_1676_ = v_item_1667_;
goto v___jp_1675_;
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec_ref(v_item_1667_);
lean_dec_ref(v_config_1666_);
v_a_2512_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_1680_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_1680_);
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
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_1678_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1676_, v___x_1677_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_2520_, lean_object* v_item_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(v_config_2520_, v_item_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object* v_e_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_2532_, v___y_2536_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_e_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(v_e_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object* v_00_u03b1_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(v_00_u03b1_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object* v_00_u03b1_2568_, lean_object* v_msg_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2578_, lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(v_00_u03b1_2578_, v_msg_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object* v_msgData_2588_, lean_object* v_macroStack_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_2588_, v_macroStack_2589_, v___y_2594_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object* v_msgData_2598_, lean_object* v_macroStack_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(v_msgData_2598_, v_macroStack_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2607_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_box(0);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_2610_ = l_Lean_mkConst(v___x_2609_, v___x_2608_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(lean_object* v_cfg_2613_, lean_object* v_cfgItem_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1);
v___x_2623_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2613_, v_cfgItem_2614_, v___x_2622_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_2624_, lean_object* v_cfgItem_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(v_cfg_2624_, v_cfgItem_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v_cfgItem_2625_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object* v_cfg_2635_, lean_object* v_init_2636_, uint8_t v_logExceptions_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_onErr_2642_; lean_object* v_eval_2643_; 
v_onErr_2642_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0));
v_eval_2643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_2637_ == 0)
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2643_, v_init_2636_, v_cfg_2635_, v_onErr_2642_, v_logExceptions_2637_, v_a_2639_, v_a_2640_);
return v___x_2644_;
}
else
{
uint8_t v_recover_2645_; lean_object* v___x_2646_; 
v_recover_2645_ = lean_ctor_get_uint8(v_a_2638_, sizeof(void*)*1);
v___x_2646_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2643_, v_init_2636_, v_cfg_2635_, v_onErr_2642_, v_recover_2645_, v_a_2639_, v_a_2640_);
return v___x_2646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_2647_, lean_object* v_init_2648_, lean_object* v_logExceptions_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
uint8_t v_logExceptions_boxed_2654_; lean_object* v_res_2655_; 
v_logExceptions_boxed_2654_ = lean_unbox(v_logExceptions_2649_);
v_res_2655_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2647_, v_init_2648_, v_logExceptions_boxed_2654_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_a_2650_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(lean_object* v_cfg_2656_, lean_object* v_init_2657_, uint8_t v_logExceptions_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2656_, v_init_2657_, v_logExceptions_2658_, v_a_2659_, v_a_2665_, v_a_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___boxed(lean_object* v_cfg_2669_, lean_object* v_init_2670_, lean_object* v_logExceptions_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
uint8_t v_logExceptions_boxed_2681_; lean_object* v_res_2682_; 
v_logExceptions_boxed_2681_ = lean_unbox(v_logExceptions_2671_);
v_res_2682_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(v_cfg_2669_, v_init_2670_, v_logExceptions_boxed_2681_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
return v_res_2682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2687_ = lean_unsigned_to_nat(0u);
v___x_2688_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
lean_ctor_set(v___x_2688_, 2, v___x_2687_);
lean_ctor_set(v___x_2688_, 3, v___x_2687_);
lean_ctor_set(v___x_2688_, 4, v___x_2686_);
lean_ctor_set(v___x_2688_, 5, v___x_2686_);
lean_ctor_set(v___x_2688_, 6, v___x_2686_);
lean_ctor_set(v___x_2688_, 7, v___x_2686_);
lean_ctor_set(v___x_2688_, 8, v___x_2686_);
lean_ctor_set(v___x_2688_, 9, v___x_2686_);
lean_ctor_set(v___x_2688_, 10, v___x_2686_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = lean_unsigned_to_nat(32u);
v___x_2690_ = lean_mk_empty_array_with_capacity(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2692_ = ((size_t)5ULL);
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = lean_unsigned_to_nat(32u);
v___x_2695_ = lean_mk_empty_array_with_capacity(v___x_2694_);
v___x_2696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3);
v___x_2697_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v___x_2695_);
lean_ctor_set(v___x_2697_, 2, v___x_2693_);
lean_ctor_set(v___x_2697_, 3, v___x_2693_);
lean_ctor_set_usize(v___x_2697_, 4, v___x_2692_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2698_ = lean_box(1);
v___x_2699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4);
v___x_2700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v___x_2699_);
lean_ctor_set(v___x_2701_, 2, v___x_2698_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__6));
v___x_2704_ = l_Lean_stringToMessageData(v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__8));
v___x_2707_ = l_Lean_stringToMessageData(v___x_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__10));
v___x_2710_ = l_Lean_stringToMessageData(v___x_2709_);
return v___x_2710_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__12));
v___x_2713_ = l_Lean_stringToMessageData(v___x_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__14));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16));
v___x_2719_ = l_Lean_stringToMessageData(v___x_2718_);
return v___x_2719_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18));
v___x_2722_ = l_Lean_stringToMessageData(v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_msg_2723_, lean_object* v_declHint_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_env_2729_; uint8_t v___x_2730_; 
v___x_2727_ = lean_box(0);
v___x_2728_ = lean_st_ref_get(v___y_2725_);
v_env_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc_ref(v_env_2729_);
lean_dec(v___x_2728_);
v___x_2730_ = l_Lean_Name_isAnonymous(v_declHint_2724_);
if (v___x_2730_ == 0)
{
uint8_t v_isExporting_2731_; 
v_isExporting_2731_ = lean_ctor_get_uint8(v_env_2729_, sizeof(void*)*13);
if (v_isExporting_2731_ == 0)
{
lean_object* v___x_2732_; 
lean_dec_ref(v_env_2729_);
lean_dec(v_declHint_2724_);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_msg_2723_);
return v___x_2732_;
}
else
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
lean_inc_ref(v_env_2729_);
v___x_2733_ = l_Lean_Environment_setExporting(v_env_2729_, v___x_2730_);
lean_inc(v_declHint_2724_);
lean_inc_ref(v___x_2733_);
v___x_2734_ = l_Lean_Environment_contains(v___x_2733_, v_declHint_2724_, v_isExporting_2731_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
lean_dec_ref(v___x_2733_);
lean_dec_ref(v_env_2729_);
lean_dec(v_declHint_2724_);
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_msg_2723_);
return v___x_2735_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v_c_2741_; lean_object* v___x_2742_; 
v___x_2736_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
v___x_2738_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2733_);
v___x_2739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2733_);
lean_ctor_set(v___x_2739_, 1, v___x_2736_);
lean_ctor_set(v___x_2739_, 2, v___x_2737_);
lean_ctor_set(v___x_2739_, 3, v___x_2738_);
lean_inc(v_declHint_2724_);
v___x_2740_ = l_Lean_MessageData_ofConstName(v_declHint_2724_, v___x_2730_);
v_c_2741_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2741_, 0, v___x_2739_);
lean_ctor_set(v_c_2741_, 1, v___x_2740_);
v___x_2742_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2733_, v_declHint_2724_);
lean_dec_ref(v___x_2733_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec_ref(v_env_2729_);
lean_dec(v_declHint_2724_);
v___x_2743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v_c_2741_);
v___x_2745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = l_Lean_MessageData_note(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v_msg_2723_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
else
{
lean_object* v_val_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2784_; 
v_val_2750_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2752_ = v___x_2742_;
v_isShared_2753_ = v_isSharedCheck_2784_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_val_2750_);
lean_dec(v___x_2742_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2784_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v_moduleNames_2755_; lean_object* v_mod_2756_; uint8_t v___x_2757_; 
v___x_2754_ = l_Lean_Environment_header(v_env_2729_);
lean_dec_ref(v_env_2729_);
v_moduleNames_2755_ = lean_ctor_get(v___x_2754_, 4);
lean_inc_ref(v_moduleNames_2755_);
lean_dec_ref(v___x_2754_);
v_mod_2756_ = lean_array_get(v___x_2727_, v_moduleNames_2755_, v_val_2750_);
lean_dec(v_val_2750_);
lean_dec_ref(v_moduleNames_2755_);
v___x_2757_ = l_Lean_isPrivateName(v_declHint_2724_);
lean_dec(v_declHint_2724_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v_c_2741_);
v___x_2760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13);
v___x_2761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = l_Lean_MessageData_ofName(v_mod_2756_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l_Lean_MessageData_note(v___x_2765_);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_msg_2723_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set_tag(v___x_2752_, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2767_);
v___x_2769_ = v___x_2752_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v_c_2741_);
v___x_2773_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17);
v___x_2774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = l_Lean_MessageData_ofName(v_mod_2756_);
v___x_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19);
v___x_2778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = l_Lean_MessageData_note(v___x_2778_);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_msg_2723_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set_tag(v___x_2752_, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2780_);
v___x_2782_ = v___x_2752_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2785_; 
lean_dec_ref(v_env_2729_);
lean_dec(v_declHint_2724_);
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_msg_2723_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2786_, lean_object* v_declHint_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2786_, v_declHint_2787_, v___y_2788_);
lean_dec(v___y_2788_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_msg_2791_, lean_object* v_declHint_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2806_; 
v___x_2796_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2791_, v_declHint_2792_, v___y_2794_);
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2801_ = l_Lean_unknownIdentifierMessageTag;
v___x_2802_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
lean_ctor_set(v___x_2802_, 1, v_a_2797_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2802_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_msg_2807_, lean_object* v_declHint_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2807_, v_declHint_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(lean_object* v_msgData_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; lean_object* v_toCold_2818_; lean_object* v_env_2819_; lean_object* v_options_2820_; uint8_t v___x_2821_; lean_object* v_env_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2817_ = lean_st_ref_get(v___y_2815_);
v_toCold_2818_ = lean_ctor_get(v___y_2814_, 0);
v_env_2819_ = lean_ctor_get(v___x_2817_, 0);
lean_inc_ref(v_env_2819_);
lean_dec(v___x_2817_);
v_options_2820_ = lean_ctor_get(v_toCold_2818_, 2);
v___x_2821_ = 0;
v_env_2822_ = l_Lean_Environment_setRecordingDeps(v_env_2819_, v___x_2821_);
v___x_2823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2824_ = lean_unsigned_to_nat(32u);
v___x_2825_ = lean_mk_empty_array_with_capacity(v___x_2824_);
lean_dec_ref(v___x_2825_);
v___x_2826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2820_);
v___x_2827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2827_, 0, v_env_2822_);
lean_ctor_set(v___x_2827_, 1, v___x_2823_);
lean_ctor_set(v___x_2827_, 2, v___x_2826_);
lean_ctor_set(v___x_2827_, 3, v_options_2820_);
v___x_2828_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
lean_ctor_set(v___x_2828_, 1, v_msgData_2813_);
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msgData_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_msg_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_ref_2839_; lean_object* v___x_2840_; lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2849_; 
v_ref_2839_ = lean_ctor_get(v___y_2836_, 2);
v___x_2840_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msg_2835_, v___y_2836_, v___y_2837_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
lean_inc(v_ref_2839_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v_ref_2839_);
lean_ctor_set(v___x_2845_, 1, v_a_2841_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_msg_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_ref_2855_, lean_object* v_msg_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_toCold_2860_; lean_object* v_currRecDepth_2861_; lean_object* v_ref_2862_; uint16_t v_optionFlags_2863_; uint8_t v_suppressElabErrors_2864_; uint8_t v_checkDeprecated_2865_; uint8_t v_isRecordingDeps_2866_; lean_object* v_ref_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_toCold_2860_ = lean_ctor_get(v___y_2857_, 0);
v_currRecDepth_2861_ = lean_ctor_get(v___y_2857_, 1);
v_ref_2862_ = lean_ctor_get(v___y_2857_, 2);
v_optionFlags_2863_ = lean_ctor_get_uint16(v___y_2857_, sizeof(void*)*3);
v_suppressElabErrors_2864_ = lean_ctor_get_uint8(v___y_2857_, sizeof(void*)*3 + 2);
v_checkDeprecated_2865_ = lean_ctor_get_uint8(v___y_2857_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2866_ = lean_ctor_get_uint8(v___y_2857_, sizeof(void*)*3 + 4);
v_ref_2867_ = l_Lean_replaceRef(v_ref_2855_, v_ref_2862_);
lean_inc(v_currRecDepth_2861_);
lean_inc_ref(v_toCold_2860_);
v___x_2868_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2868_, 0, v_toCold_2860_);
lean_ctor_set(v___x_2868_, 1, v_currRecDepth_2861_);
lean_ctor_set(v___x_2868_, 2, v_ref_2867_);
lean_ctor_set_uint16(v___x_2868_, sizeof(void*)*3, v_optionFlags_2863_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*3 + 2, v_suppressElabErrors_2864_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*3 + 3, v_checkDeprecated_2865_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*3 + 4, v_isRecordingDeps_2866_);
v___x_2869_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2856_, v___x_2868_, v___y_2858_);
lean_dec_ref_known(v___x_2868_, 3);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_ref_2870_, lean_object* v_msg_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2870_, v_msg_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_ref_2870_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2876_, lean_object* v_msg_2877_, lean_object* v_declHint_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2882_; lean_object* v_a_2883_; lean_object* v___x_2884_; 
v___x_2882_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2877_, v_declHint_2878_, v___y_2879_, v___y_2880_);
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2876_, v_a_2883_, v___y_2879_, v___y_2880_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2885_, lean_object* v_msg_2886_, lean_object* v_declHint_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2885_, v_msg_2886_, v_declHint_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v_ref_2885_);
return v_res_2891_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2895_, lean_object* v_constName_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; uint8_t v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2900_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2901_ = 0;
lean_inc(v_constName_2896_);
v___x_2902_ = l_Lean_MessageData_ofConstName(v_constName_2896_, v___x_2901_);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2900_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2895_, v___x_2905_, v_constName_2896_, v___y_2897_, v___y_2898_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2907_, lean_object* v_constName_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_2907_, v_constName_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v_ref_2907_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(lean_object* v_constName_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_ref_2917_; lean_object* v___x_2918_; 
v_ref_2917_ = lean_ctor_get(v___y_2914_, 2);
v___x_2918_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_2917_, v_constName_2913_, v___y_2914_, v___y_2915_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(lean_object* v_constName_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; lean_object* v_env_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; 
v___x_2928_ = lean_st_ref_get(v___y_2926_);
v_env_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc_ref(v_env_2929_);
lean_dec(v___x_2928_);
v___x_2930_ = 0;
lean_inc(v_constName_2924_);
v___x_2931_ = l_Lean_Environment_find_x3f(v_env_2929_, v_constName_2924_, v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_2924_, v___y_2925_, v___y_2926_);
return v___x_2932_;
}
else
{
lean_object* v_val_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v_constName_2924_);
v_val_2933_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2931_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_val_2933_);
lean_dec(v___x_2931_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 0);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_val_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0___boxed(lean_object* v_constName_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_constName_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(uint8_t v___x_2946_, lean_object* v_x_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
if (lean_obj_tag(v_x_2947_) == 0)
{
uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = 1;
v___x_2952_ = lean_box(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
return v___x_2953_;
}
else
{
lean_object* v_head_2954_; lean_object* v_tail_2955_; lean_object* v___y_2957_; uint8_t v_a_2958_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_head_2954_ = lean_ctor_get(v_x_2947_, 0);
lean_inc(v_head_2954_);
v_tail_2955_ = lean_ctor_get(v_x_2947_, 1);
lean_inc(v_tail_2955_);
lean_dec_ref_known(v_x_2947_, 2);
v___x_2960_ = lean_unsigned_to_nat(0u);
v___x_2961_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_head_2954_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2977_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2977_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2977_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
if (lean_obj_tag(v_a_2962_) == 6)
{
lean_object* v_val_2966_; lean_object* v_numFields_2967_; uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
v_val_2966_ = lean_ctor_get(v_a_2962_, 0);
lean_inc_ref(v_val_2966_);
lean_dec_ref_known(v_a_2962_, 1);
v_numFields_2967_ = lean_ctor_get(v_val_2966_, 4);
lean_inc(v_numFields_2967_);
lean_dec_ref(v_val_2966_);
v___x_2968_ = lean_nat_dec_eq(v_numFields_2967_, v___x_2960_);
lean_dec(v_numFields_2967_);
v___x_2969_ = lean_box(v___x_2968_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2969_);
v___x_2971_ = v___x_2964_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
v___y_2957_ = v___x_2971_;
v_a_2958_ = v___x_2968_;
goto v___jp_2956_;
}
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_dec(v_a_2962_);
v___x_2973_ = lean_box(v___x_2946_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2973_);
v___x_2975_ = v___x_2964_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v___y_2957_ = v___x_2975_;
v_a_2958_ = v___x_2946_;
goto v___jp_2956_;
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v_tail_2955_);
v_a_2978_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2961_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2961_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
v___jp_2956_:
{
if (v_a_2958_ == 0)
{
lean_dec(v_tail_2955_);
return v___y_2957_;
}
else
{
lean_dec_ref(v___y_2957_);
v_x_2947_ = v_tail_2955_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2___boxed(lean_object* v___x_2986_, lean_object* v_x_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
uint8_t v___x_4250__boxed_2991_; lean_object* v_res_2992_; 
v___x_4250__boxed_2991_ = lean_unbox(v___x_2986_);
v_res_2992_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v___x_4250__boxed_2991_, v_x_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(lean_object* v_declName_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3053_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3053_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3053_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
if (lean_obj_tag(v_a_2998_) == 5)
{
lean_object* v_val_3002_; lean_object* v_toConstantVal_3003_; lean_object* v_numParams_3004_; lean_object* v_numIndices_3005_; lean_object* v_ctors_3006_; uint8_t v_isRec_3007_; uint8_t v_isUnsafe_3008_; lean_object* v_type_3009_; uint8_t v___x_3010_; 
v_val_3002_ = lean_ctor_get(v_a_2998_, 0);
lean_inc_ref(v_val_3002_);
lean_dec_ref_known(v_a_2998_, 1);
v_toConstantVal_3003_ = lean_ctor_get(v_val_3002_, 0);
v_numParams_3004_ = lean_ctor_get(v_val_3002_, 1);
lean_inc(v_numParams_3004_);
v_numIndices_3005_ = lean_ctor_get(v_val_3002_, 2);
lean_inc(v_numIndices_3005_);
v_ctors_3006_ = lean_ctor_get(v_val_3002_, 4);
lean_inc(v_ctors_3006_);
v_isRec_3007_ = lean_ctor_get_uint8(v_val_3002_, sizeof(void*)*6);
v_isUnsafe_3008_ = lean_ctor_get_uint8(v_val_3002_, sizeof(void*)*6 + 1);
v_type_3009_ = lean_ctor_get(v_toConstantVal_3003_, 2);
v___x_3010_ = l_Lean_Expr_isProp(v_type_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3011_ = l_Lean_InductiveVal_numTypeFormers(v_val_3002_);
lean_dec_ref(v_val_3002_);
v___x_3012_ = lean_unsigned_to_nat(1u);
v___x_3013_ = lean_nat_dec_eq(v___x_3011_, v___x_3012_);
lean_dec(v___x_3011_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3016_; 
lean_dec(v_ctors_3006_);
lean_dec(v_numIndices_3005_);
lean_dec(v_numParams_3004_);
v___x_3014_ = lean_box(v___x_3013_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3014_);
v___x_3016_ = v___x_3000_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
else
{
lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3019_ = lean_nat_dec_eq(v_numIndices_3005_, v___x_3018_);
lean_dec(v_numIndices_3005_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
lean_dec(v_ctors_3006_);
lean_dec(v_numParams_3004_);
v___x_3020_ = lean_box(v___x_3019_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3020_);
v___x_3022_ = v___x_3000_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
else
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_nat_dec_eq(v_numParams_3004_, v___x_3018_);
lean_dec(v_numParams_3004_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3027_; 
lean_dec(v_ctors_3006_);
v___x_3025_ = lean_box(v___x_3024_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3025_);
v___x_3027_ = v___x_3000_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
else
{
uint8_t v___x_3029_; 
v___x_3029_ = l_List_isEmpty___redArg(v_ctors_3006_);
if (v___x_3029_ == 0)
{
if (v_isRec_3007_ == 0)
{
if (v_isUnsafe_3008_ == 0)
{
lean_object* v___x_3030_; 
lean_del_object(v___x_3000_);
v___x_3030_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v_isUnsafe_3008_, v_ctors_3006_, v___y_2994_, v___y_2995_);
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; lean_object* v___x_3033_; 
lean_dec(v_ctors_3006_);
v___x_3031_ = lean_box(v_isRec_3007_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3031_);
v___x_3033_ = v___x_3000_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v___x_3035_; lean_object* v___x_3037_; 
lean_dec(v_ctors_3006_);
v___x_3035_ = lean_box(v___x_3029_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3035_);
v___x_3037_ = v___x_3000_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_dec(v_ctors_3006_);
v___x_3039_ = lean_box(v___x_3010_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3039_);
v___x_3041_ = v___x_3000_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
}
else
{
uint8_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
lean_dec(v_ctors_3006_);
lean_dec(v_numIndices_3005_);
lean_dec(v_numParams_3004_);
lean_dec_ref(v_val_3002_);
v___x_3043_ = 0;
v___x_3044_ = lean_box(v___x_3043_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3044_);
v___x_3046_ = v___x_3000_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
lean_dec(v_a_2998_);
v___x_3048_ = 0;
v___x_3049_ = lean_box(v___x_3048_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3049_);
v___x_3051_ = v___x_3000_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3049_);
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
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v_a_3054_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2997_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2997_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
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
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1___boxed(lean_object* v_declName_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object* v_cfg_3067_, lean_object* v_declName_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
uint8_t v_structures_3072_; uint8_t v_enums_3073_; uint8_t v_a_3075_; 
v_structures_3072_ = lean_ctor_get_uint8(v_cfg_3067_, sizeof(void*)*3 + 5);
v_enums_3073_ = lean_ctor_get_uint8(v_cfg_3067_, sizeof(void*)*3 + 7);
if (v_enums_3073_ == 0)
{
v_a_3075_ = v_enums_3073_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3113_; 
lean_inc(v_declName_3068_);
v___x_3113_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3124_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3124_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3124_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
uint8_t v___x_3118_; 
v___x_3118_ = lean_unbox(v_a_3114_);
if (v___x_3118_ == 0)
{
uint8_t v___x_3119_; 
lean_del_object(v___x_3116_);
v___x_3119_ = lean_unbox(v_a_3114_);
lean_dec(v_a_3114_);
v_a_3075_ = v___x_3119_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_dec(v_a_3114_);
lean_dec(v_declName_3068_);
v___x_3120_ = lean_box(v_enums_3073_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3120_);
v___x_3122_ = v___x_3116_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
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
else
{
lean_dec(v_declName_3068_);
return v___x_3113_;
}
}
v___jp_3074_:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_st_ref_get(v_a_3070_);
if (v_structures_3072_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec(v___x_3076_);
lean_dec(v_declName_3068_);
v___x_3077_ = lean_box(v_a_3075_);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
return v___x_3078_;
}
else
{
if (v_a_3075_ == 0)
{
lean_object* v_env_3079_; uint8_t v___x_3080_; 
v_env_3079_ = lean_ctor_get(v___x_3076_, 0);
lean_inc_ref(v_env_3079_);
lean_dec(v___x_3076_);
lean_inc(v_declName_3068_);
v___x_3080_ = l_Lean_isStructure(v_env_3079_, v_declName_3068_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec(v_declName_3068_);
v___x_3081_ = lean_box(v_a_3075_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
else
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_3068_, v_a_3069_, v_a_3070_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3102_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3102_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3102_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
if (lean_obj_tag(v_a_3084_) == 5)
{
lean_object* v_val_3088_; uint8_t v_isRec_3089_; 
v_val_3088_ = lean_ctor_get(v_a_3084_, 0);
lean_inc_ref(v_val_3088_);
lean_dec_ref_known(v_a_3084_, 1);
v_isRec_3089_ = lean_ctor_get_uint8(v_val_3088_, sizeof(void*)*6);
lean_dec_ref(v_val_3088_);
if (v_isRec_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3090_ = lean_box(v___x_3080_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3090_);
v___x_3092_ = v___x_3086_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_box(v_a_3075_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3094_);
v___x_3096_ = v___x_3086_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
lean_dec(v_a_3084_);
v___x_3098_ = lean_box(v_a_3075_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3098_);
v___x_3100_ = v___x_3086_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_a_3103_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3083_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3083_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec(v___x_3076_);
lean_dec(v_declName_3068_);
v___x_3111_ = lean_box(v_a_3075_);
v___x_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
return v___x_3112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType___boxed(lean_object* v_cfg_3125_, lean_object* v_declName_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3125_, v_declName_3126_, v_a_3127_, v_a_3128_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec_ref(v_cfg_3125_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(lean_object* v_00_u03b1_3131_, lean_object* v_constName_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_3132_, v___y_3133_, v___y_3134_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3137_, lean_object* v_constName_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(v_00_u03b1_3137_, v_constName_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3143_, lean_object* v_ref_3144_, lean_object* v_constName_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_3144_, v_constName_3145_, v___y_3146_, v___y_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3150_, lean_object* v_ref_3151_, lean_object* v_constName_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(v_00_u03b1_3150_, v_ref_3151_, v_constName_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v_ref_3151_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3157_, lean_object* v_ref_3158_, lean_object* v_msg_3159_, lean_object* v_declHint_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3158_, v_msg_3159_, v_declHint_3160_, v___y_3161_, v___y_3162_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3165_, lean_object* v_ref_3166_, lean_object* v_msg_3167_, lean_object* v_declHint_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3165_, v_ref_3166_, v_msg_3167_, v_declHint_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v_ref_3166_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_3173_, lean_object* v_declHint_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_3173_, v_declHint_3174_, v___y_3176_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3179_, lean_object* v_declHint_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3179_, v_declHint_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b1_3185_, lean_object* v_ref_3186_, lean_object* v_msg_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_3186_, v_msg_3187_, v___y_3188_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b1_3192_, lean_object* v_ref_3193_, lean_object* v_msg_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03b1_3192_, v_ref_3193_, v_msg_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v_ref_3193_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b1_3199_, lean_object* v_msg_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_3200_, v___y_3201_, v___y_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3205_, lean_object* v_msg_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(v_00_u03b1_3205_, v_msg_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3210_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(lean_object* v_a_3211_, lean_object* v_as_3212_, size_t v_i_3213_, size_t v_stop_3214_){
_start:
{
uint8_t v___x_3215_; 
v___x_3215_ = lean_usize_dec_eq(v_i_3213_, v_stop_3214_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = lean_array_uget_borrowed(v_as_3212_, v_i_3213_);
v___x_3217_ = lean_name_eq(v_a_3211_, v___x_3216_);
if (v___x_3217_ == 0)
{
size_t v___x_3218_; size_t v___x_3219_; 
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_add(v_i_3213_, v___x_3218_);
v_i_3213_ = v___x_3219_;
goto _start;
}
else
{
return v___x_3217_;
}
}
else
{
uint8_t v___x_3221_; 
v___x_3221_ = 0;
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0___boxed(lean_object* v_a_3222_, lean_object* v_as_3223_, lean_object* v_i_3224_, lean_object* v_stop_3225_){
_start:
{
size_t v_i_boxed_3226_; size_t v_stop_boxed_3227_; uint8_t v_res_3228_; lean_object* v_r_3229_; 
v_i_boxed_3226_ = lean_unbox_usize(v_i_3224_);
lean_dec(v_i_3224_);
v_stop_boxed_3227_ = lean_unbox_usize(v_stop_3225_);
lean_dec(v_stop_3225_);
v_res_3228_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3222_, v_as_3223_, v_i_boxed_3226_, v_stop_boxed_3227_);
lean_dec_ref(v_as_3223_);
lean_dec(v_a_3222_);
v_r_3229_ = lean_box(v_res_3228_);
return v_r_3229_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(lean_object* v_as_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3232_ = lean_unsigned_to_nat(0u);
v___x_3233_ = lean_array_get_size(v_as_3230_);
v___x_3234_ = lean_nat_dec_lt(v___x_3232_, v___x_3233_);
if (v___x_3234_ == 0)
{
return v___x_3234_;
}
else
{
size_t v___x_3235_; size_t v___x_3236_; uint8_t v___x_3237_; 
v___x_3235_ = ((size_t)0ULL);
v___x_3236_ = lean_usize_of_nat(v___x_3233_);
v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3231_, v_as_3230_, v___x_3235_, v___x_3236_);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0___boxed(lean_object* v_as_3238_, lean_object* v_a_3239_){
_start:
{
uint8_t v_res_3240_; lean_object* v_r_3241_; 
v_res_3240_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_as_3238_, v_a_3239_);
lean_dec(v_a_3239_);
lean_dec_ref(v_as_3238_);
v_r_3241_ = lean_box(v_res_3240_);
return v_r_3241_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__0));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(lean_object* v_cfg_3245_, lean_object* v_as_3246_, size_t v_sz_3247_, size_t v_i_3248_, lean_object* v_b_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_a_3254_; uint8_t v___x_3258_; 
v___x_3258_ = lean_usize_dec_lt(v_i_3248_, v_sz_3247_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_b_3249_);
return v___x_3259_;
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_a_3260_ = lean_array_uget_borrowed(v_as_3246_, v_i_3248_);
v___x_3261_ = lean_box(0);
lean_inc(v_a_3260_);
v___x_3262_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_3260_, v___x_3261_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3267_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc_n(v_a_3263_, 2);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3267_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3245_, v_a_3263_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; uint8_t v___x_3269_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3267_, 1);
v___x_3269_ = lean_unbox(v_a_3268_);
lean_dec(v_a_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3270_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
lean_inc(v_a_3263_);
v___x_3271_ = l_Lean_MessageData_ofName(v_a_3263_);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_a_3260_, v___x_3274_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_dec_ref_known(v___x_3275_, 1);
goto v___jp_3264_;
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec(v_a_3263_);
lean_dec_ref(v_b_3249_);
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
else
{
goto v___jp_3264_;
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_a_3263_);
lean_dec_ref(v_b_3249_);
v_a_3284_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3267_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3267_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
v___jp_3264_:
{
uint8_t v___x_3265_; 
v___x_3265_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_b_3249_, v_a_3263_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_array_push(v_b_3249_, v_a_3263_);
v_a_3254_ = v___x_3266_;
goto v___jp_3253_;
}
else
{
lean_dec(v_a_3263_);
v_a_3254_ = v_b_3249_;
goto v___jp_3253_;
}
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec_ref(v_b_3249_);
v_a_3292_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3262_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3262_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
v___jp_3253_:
{
size_t v___x_3255_; size_t v___x_3256_; 
v___x_3255_ = ((size_t)1ULL);
v___x_3256_ = lean_usize_add(v_i_3248_, v___x_3255_);
v_i_3248_ = v___x_3256_;
v_b_3249_ = v_a_3254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___boxed(lean_object* v_cfg_3300_, lean_object* v_as_3301_, lean_object* v_sz_3302_, lean_object* v_i_3303_, lean_object* v_b_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
size_t v_sz_boxed_3308_; size_t v_i_boxed_3309_; lean_object* v_res_3310_; 
v_sz_boxed_3308_ = lean_unbox_usize(v_sz_3302_);
lean_dec(v_sz_3302_);
v_i_boxed_3309_ = lean_unbox_usize(v_i_3303_);
lean_dec(v_i_3303_);
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3300_, v_as_3301_, v_sz_boxed_3308_, v_i_boxed_3309_, v_b_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec_ref(v_as_3301_);
lean_dec_ref(v_cfg_3300_);
return v_res_3310_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__3));
v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object* v_stx_3323_, lean_object* v_cfg_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
if (lean_obj_tag(v_stx_3323_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3363_; 
v_val_3328_ = lean_ctor_get(v_stx_3323_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_stx_3323_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3330_ = v_stx_3323_;
v_isShared_3331_ = v_isSharedCheck_3363_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_val_3328_);
lean_dec(v_stx_3323_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3363_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3332_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2));
lean_inc(v_val_3328_);
v___x_3333_ = l_Lean_Syntax_isOfKind(v_val_3328_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_del_object(v___x_3330_);
v___x_3334_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4);
v___x_3335_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_val_3328_, v___x_3334_, v_a_3325_, v_a_3326_);
lean_dec(v_val_3328_);
return v___x_3335_;
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_ids_3338_; lean_object* v_types_3339_; lean_object* v___x_3340_; size_t v_sz_3341_; size_t v___x_3342_; lean_object* v___x_3343_; 
v___x_3336_ = lean_unsigned_to_nat(2u);
v___x_3337_ = l_Lean_Syntax_getArg(v_val_3328_, v___x_3336_);
lean_dec(v_val_3328_);
v_ids_3338_ = l_Lean_Syntax_getArgs(v___x_3337_);
lean_dec(v___x_3337_);
v_types_3339_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__5));
v___x_3340_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ids_3338_);
lean_dec_ref(v_ids_3338_);
v_sz_3341_ = lean_array_size(v___x_3340_);
v___x_3342_ = ((size_t)0ULL);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3324_, v___x_3340_, v_sz_3341_, v___x_3342_, v_types_3339_, v_a_3325_, v_a_3326_);
lean_dec_ref(v___x_3340_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3354_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3354_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3354_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v_a_3344_);
v___x_3349_ = v___x_3330_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3349_);
v___x_3351_ = v___x_3346_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_del_object(v___x_3330_);
v_a_3355_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3343_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3343_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_dec(v_stx_3323_);
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
return v___x_3365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___boxed(lean_object* v_stx_3366_, lean_object* v_cfg_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_stx_3366_, v_cfg_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec_ref(v_cfg_3367_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3387_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3384_, v___x_3385_, v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2____boxed(lean_object* v_a_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_();
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3410_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3407_, v___x_3408_, v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2____boxed(lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3422_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3425_ = l_Lean_Meta_registerSimpAttr(v___x_3422_, v___x_3423_, v___x_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2____boxed(lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(lean_object* v_e_3428_){
_start:
{
if (lean_obj_tag(v_e_3428_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3438_; 
v_a_3430_ = lean_ctor_get(v_e_3428_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_e_3428_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3432_ = v_e_3428_;
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v_e_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3438_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3434_ = lean_mk_io_user_error(v_a_3430_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 1);
lean_ctor_set(v___x_3432_, 0, v___x_3434_);
v___x_3436_ = v___x_3432_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
v_a_3439_ = lean_ctor_get(v_e_3428_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_e_3428_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v_e_3428_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v_e_3428_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set_tag(v___x_3441_, 0);
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_e_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3447_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3450_, lean_object* v_e_3451_){
_start:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3451_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3454_, lean_object* v_e_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(v_00_u03b1_3454_, v_e_3455_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v_declName_3458_, lean_object* v_stx_3459_, uint8_t v_attrKind_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v___x_3464_; lean_object* v_env_3465_; lean_object* v_ref_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3464_ = lean_st_ref_get(v___y_3462_);
v_env_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc_ref_n(v_env_3465_, 2);
lean_dec(v___x_3464_);
v_ref_3466_ = lean_ctor_get(v___y_3461_, 2);
v___x_3467_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3468_ = l_Lean_getAttributeImpl(v_env_3465_, v___x_3467_);
v___x_3469_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3468_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v_add_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v_add_3471_ = lean_ctor_get(v_a_3470_, 1);
lean_inc_ref(v_add_3471_);
lean_dec(v_a_3470_);
v___x_3472_ = lean_box(v_attrKind_3460_);
lean_inc(v___y_3462_);
lean_inc_ref(v___y_3461_);
lean_inc(v_stx_3459_);
lean_inc(v_declName_3458_);
v___x_3473_ = lean_apply_6(v_add_3471_, v_declName_3458_, v_stx_3459_, v___x_3472_, v___y_3461_, v___y_3462_, lean_box(0));
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3498_; 
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v___x_3473_, 0);
lean_dec(v_unused_3499_);
v___x_3475_ = v___x_3473_;
v_isShared_3476_ = v_isSharedCheck_3498_;
goto v_resetjp_3474_;
}
else
{
lean_dec(v___x_3473_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3498_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3477_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3478_ = l_Lean_getAttributeImpl(v_env_3465_, v___x_3477_);
v___x_3479_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3478_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v_add_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_del_object(v___x_3475_);
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v_add_3481_ = lean_ctor_get(v_a_3480_, 1);
lean_inc_ref(v_add_3481_);
lean_dec(v_a_3480_);
v___x_3482_ = lean_box(v_attrKind_3460_);
lean_inc(v___y_3462_);
lean_inc_ref(v___y_3461_);
v___x_3483_ = lean_apply_6(v_add_3481_, v_declName_3458_, v_stx_3459_, v___x_3482_, v___y_3461_, v___y_3462_, lean_box(0));
return v___x_3483_;
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_stx_3459_);
lean_dec(v_declName_3458_);
v_a_3484_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3486_ = v___x_3479_;
v_isShared_3487_ = v_isSharedCheck_3497_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3479_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3497_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3488_ = lean_io_error_to_string(v_a_3484_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set_tag(v___x_3475_, 3);
lean_ctor_set(v___x_3475_, 0, v___x_3488_);
v___x_3490_ = v___x_3475_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3491_ = l_Lean_MessageData_ofFormat(v___x_3490_);
lean_inc(v_ref_3466_);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v_ref_3466_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3492_);
v___x_3494_ = v___x_3486_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_3465_);
lean_dec(v_stx_3459_);
lean_dec(v_declName_3458_);
return v___x_3473_;
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_env_3465_);
lean_dec(v_stx_3459_);
lean_dec(v_declName_3458_);
v_a_3500_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3502_ = v___x_3469_;
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3469_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3509_; 
v___x_3504_ = lean_io_error_to_string(v_a_3500_);
v___x_3505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
v___x_3506_ = l_Lean_MessageData_ofFormat(v___x_3505_);
lean_inc(v_ref_3466_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v_ref_3466_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3507_);
v___x_3509_ = v___x_3502_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_declName_3512_, lean_object* v_stx_3513_, lean_object* v_attrKind_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v_attrKind_boxed_3518_; lean_object* v_res_3519_; 
v_attrKind_boxed_3518_ = lean_unbox(v_attrKind_3514_);
v_res_3519_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v_declName_3512_, v_stx_3513_, v_attrKind_boxed_3518_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3525_ = l_Lean_stringToMessageData(v___x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v___x_3526_, lean_object* v_decl_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3532_ = l_Lean_MessageData_ofName(v___x_3526_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v___x_3535_, v___y_3528_, v___y_3529_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v___x_3537_, lean_object* v_decl_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v___x_3537_, v_decl_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v_decl_3538_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3573_ = l_Lean_registerBuiltinAttribute(v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
return v_res_3575_;
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
