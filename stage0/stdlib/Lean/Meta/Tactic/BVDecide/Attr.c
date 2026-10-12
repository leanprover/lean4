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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__27;
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
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_();
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_();
return v_res_89_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_unsigned_to_nat(3575118154u);
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__27_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_97_ = l_Lean_Name_num___override(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__29_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_99_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_100_ = l_Lean_Name_str___override(v___x_99_, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__31_00___x40_Lean_Meta_Tactic_BVDecide_Attr_921759773____hygCtx___hyg_2_));
v___x_102_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_103_ = l_Lean_Name_str___override(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_106_ = l_Lean_Name_num___override(v___x_105_, v___x_104_);
return v___x_106_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_));
v___x_109_ = 0;
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_);
v___x_111_ = l_Lean_registerTraceClass(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_112_;
v_res_112_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_();
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2____boxed(lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_3575118154____hygCtx___hyg_2_();
return v_res_114_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_));
v___x_135_ = 0;
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_));
v___x_137_ = l_Lean_registerTraceClass(v___x_134_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_138_;
v_res_138_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_();
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2____boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_();
return v_res_140_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object* v_name_141_, lean_object* v_decl_142_, lean_object* v_ref_143_){
_start:
{
lean_object* v_defValue_145_; lean_object* v_descr_146_; lean_object* v_deprecation_x3f_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_defValue_145_ = lean_ctor_get(v_decl_142_, 0);
v_descr_146_ = lean_ctor_get(v_decl_142_, 1);
v_deprecation_x3f_147_ = lean_ctor_get(v_decl_142_, 2);
lean_inc(v_defValue_145_);
v___x_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_148_, 0, v_defValue_145_);
lean_inc(v_deprecation_x3f_147_);
lean_inc_ref(v_descr_146_);
lean_inc_n(v_name_141_, 2);
v___x_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_149_, 0, v_name_141_);
lean_ctor_set(v___x_149_, 1, v_ref_143_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
lean_ctor_set(v___x_149_, 3, v_descr_146_);
lean_ctor_set(v___x_149_, 4, v_deprecation_x3f_147_);
v___x_150_ = lean_register_option(v_name_141_, v___x_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_159_);
v___x_152_ = v___x_150_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_dec(v___x_150_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_156_; 
lean_inc(v_defValue_145_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_name_141_);
lean_ctor_set(v___x_154_, 1, v_defValue_145_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_154_);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec(v_name_141_);
v_a_160_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_150_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_150_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_141_ = stack[0].m_obj;
lean_object* v_decl_142_ = stack[1].m_obj;
lean_object* v_ref_143_ = stack[2].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(v_name_141_, v_decl_142_, v_ref_143_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_169_, lean_object* v_decl_170_, lean_object* v_ref_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(v_name_169_, v_decl_170_, v_ref_171_);
lean_dec_ref(v_decl_170_);
return v_res_173_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__5_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_));
v___x_195_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__spec__0(v___x_192_, v___x_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_196_;
v_res_196_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_();
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1794396972____hygCtx___hyg_4_();
return v_res_198_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_box(0);
v___x_200_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
return v___x_201_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___closed__0);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_205_;
v_res_205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg___boxed(lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v_res_207_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(lean_object* v_00_u03b1_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_216_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_209_ = stack[1].m_obj;
lean_object* v___y_210_ = stack[2].m_obj;
lean_object* v___y_211_ = stack[3].m_obj;
lean_object* v___y_212_ = stack[4].m_obj;
lean_object* v___y_213_ = stack[5].m_obj;
lean_object* v___y_214_ = stack[6].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(lean_box(0), v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___boxed(lean_object* v_00_u03b1_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0(v_00_u03b1_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_226_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v___x_234_, lean_object* v_ctor_235_, lean_object* v_args_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_245_ = lean_string_dec_eq(v_ctor_235_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_247_ = lean_string_dec_eq(v_ctor_235_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_249_ = lean_string_dec_eq(v_ctor_235_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v___x_234_);
lean_dec_ref(v___x_233_);
lean_dec_ref(v___x_232_);
lean_dec_ref(v___x_231_);
lean_dec_ref(v___x_230_);
v___x_250_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_spec__0___redArg();
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = l_Lean_Name_mkStr6(v___x_230_, v___x_231_, v___x_232_, v___x_233_, v___x_234_, v___x_248_);
v___x_252_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_251_);
v___x_253_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_251_, v___x_252_, v_args_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_265_; 
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_253_, 0);
lean_dec(v_unused_266_);
v___x_255_ = v___x_253_;
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
else
{
lean_dec(v___x_253_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_257_ = 0;
v___x_258_ = lean_box(0);
v___x_259_ = l_Lean_Expr_const___override(v___x_251_, v___x_258_);
v___x_260_ = lean_box(v___x_257_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_261_);
v___x_263_ = v___x_255_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v___x_251_);
v_a_267_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_253_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_253_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = l_Lean_Name_mkStr6(v___x_230_, v___x_231_, v___x_232_, v___x_233_, v___x_234_, v___x_246_);
v___x_276_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_275_);
v___x_277_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_275_, v___x_276_, v_args_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_289_; 
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_277_, 0);
lean_dec(v_unused_290_);
v___x_279_ = v___x_277_;
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
else
{
lean_dec(v___x_277_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_281_ = 2;
v___x_282_ = lean_box(0);
v___x_283_ = l_Lean_Expr_const___override(v___x_275_, v___x_282_);
v___x_284_ = lean_box(v___x_281_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_285_);
v___x_287_ = v___x_279_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v___x_275_);
v_a_291_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_277_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_277_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Name_mkStr6(v___x_230_, v___x_231_, v___x_232_, v___x_233_, v___x_234_, v___x_244_);
v___x_300_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_299_);
v___x_301_ = l_Lean_Elab_ConfigEval_EvalTerm_checkExpectedNumberOfArguments(v___x_299_, v___x_300_, v_args_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_313_; 
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; 
v_unused_314_ = lean_ctor_get(v___x_301_, 0);
lean_dec(v_unused_314_);
v___x_303_ = v___x_301_;
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
else
{
lean_dec(v___x_301_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_313_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_305_ = 1;
v___x_306_ = lean_box(0);
v___x_307_ = l_Lean_Expr_const___override(v___x_299_, v___x_306_);
v___x_308_ = lean_box(v___x_305_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_309_);
v___x_311_ = v___x_303_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v___x_299_);
v_a_315_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_301_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_301_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_230_ = stack[0].m_obj;
lean_object* v___x_231_ = stack[1].m_obj;
lean_object* v___x_232_ = stack[2].m_obj;
lean_object* v___x_233_ = stack[3].m_obj;
lean_object* v___x_234_ = stack[4].m_obj;
lean_object* v_ctor_235_ = stack[5].m_obj;
lean_object* v_args_236_ = stack[6].m_obj;
lean_object* v___y_237_ = stack[7].m_obj;
lean_object* v___y_238_ = stack[8].m_obj;
lean_object* v___y_239_ = stack[9].m_obj;
lean_object* v___y_240_ = stack[10].m_obj;
lean_object* v___y_241_ = stack[11].m_obj;
lean_object* v___y_242_ = stack[12].m_obj;
lean_object* v_res_323_;
v_res_323_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(v___x_230_, v___x_231_, v___x_232_, v___x_233_, v___x_234_, v_ctor_235_, v_args_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___boxed(lean_object* v___x_324_, lean_object* v___x_325_, lean_object* v___x_326_, lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v_ctor_329_, lean_object* v_args_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0(v___x_324_, v___x_325_, v___x_326_, v___x_327_, v___x_328_, v_ctor_329_, v_args_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec_ref(v_args_330_);
lean_dec_ref(v_ctor_329_);
return v_res_338_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___f_361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__2));
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_363_ = l_Lean_Elab_ConfigEval_EvalTerm_withSimpleEvalStx___redArg(v___x_362_, v___f_361_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v___x_363_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_353_ = stack[0].m_obj;
lean_object* v_a_354_ = stack[1].m_obj;
lean_object* v_a_355_ = stack[2].m_obj;
lean_object* v_a_356_ = stack[3].m_obj;
lean_object* v_a_357_ = stack[4].m_obj;
lean_object* v_a_358_ = stack[5].m_obj;
lean_object* v_a_359_ = stack[6].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___boxed(lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_box(0);
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_377_ = l_Lean_Expr_const___override(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__0));
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__2);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_box(0);
v___x_383_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
return v___x_384_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___closed__0);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_388_;
v_res_388_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg___boxed(lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v_res_390_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(lean_object* v_00_u03b1_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_397_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_392_ = stack[1].m_obj;
lean_object* v___y_393_ = stack[2].m_obj;
lean_object* v___y_394_ = stack[3].m_obj;
lean_object* v___y_395_ = stack[4].m_obj;
lean_object* v_res_398_;
v_res_398_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(lean_box(0), v___y_392_, v___y_393_, v___y_394_, v___y_395_);
stack->m_obj
 = v_res_398_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0(v_00_u03b1_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_405_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(lean_object* v_msgData_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; lean_object* v_env_413_; uint8_t v___x_414_; lean_object* v_env_415_; lean_object* v___x_416_; lean_object* v_toCold_417_; lean_object* v_mctx_418_; lean_object* v_lctx_419_; lean_object* v_options_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_412_ = lean_st_ref_get(v___y_410_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc_ref(v_env_413_);
lean_dec(v___x_412_);
v___x_414_ = 0;
v_env_415_ = l_Lean_Environment_setRecordingDeps(v_env_413_, v___x_414_);
v___x_416_ = lean_st_ref_get(v___y_408_);
v_toCold_417_ = lean_ctor_get(v___y_409_, 0);
v_mctx_418_ = lean_ctor_get(v___x_416_, 0);
lean_inc_ref(v_mctx_418_);
lean_dec(v___x_416_);
v_lctx_419_ = lean_ctor_get(v___y_407_, 2);
v_options_420_ = lean_ctor_get(v_toCold_417_, 2);
lean_inc_ref(v_options_420_);
lean_inc_ref(v_lctx_419_);
v___x_421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_421_, 0, v_env_415_);
lean_ctor_set(v___x_421_, 1, v_mctx_418_);
lean_ctor_set(v___x_421_, 2, v_lctx_419_);
lean_ctor_set(v___x_421_, 3, v_options_420_);
v___x_422_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_msgData_406_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_406_ = stack[0].m_obj;
lean_object* v___y_407_ = stack[1].m_obj;
lean_object* v___y_408_ = stack[2].m_obj;
lean_object* v___y_409_ = stack[3].m_obj;
lean_object* v___y_410_ = stack[4].m_obj;
lean_object* v_res_424_;
v_res_424_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msgData_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msgData_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_431_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_ref_438_; lean_object* v___x_439_; lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_ref_438_ = lean_ctor_get(v___y_435_, 2);
v___x_439_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
lean_inc(v_ref_438_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_ref_438_);
lean_ctor_set(v___x_444_, 1, v_a_440_);
if (v_isShared_443_ == 0)
{
lean_ctor_set_tag(v___x_442_, 1);
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_432_ = stack[0].m_obj;
lean_object* v___y_433_ = stack[1].m_obj;
lean_object* v___y_434_ = stack[2].m_obj;
lean_object* v___y_435_ = stack[3].m_obj;
lean_object* v___y_436_ = stack[4].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(lean_object* v_ctor_460_, lean_object* v_args_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_480_ = lean_string_dec_eq(v_ctor_460_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_482_ = lean_string_dec_eq(v_ctor_460_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_484_ = lean_string_dec_eq(v_ctor_460_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_array_get_size(v_args_461_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_490_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_489_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
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
goto v___jp_467_;
}
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_array_get_size(v_args_461_);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v___x_502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_503_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_502_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
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
goto v___jp_471_;
}
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = lean_array_get_size(v_args_461_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_nat_dec_eq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v___x_515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_516_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_515_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
goto v___jp_475_;
}
}
v___jp_467_:
{
uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = 0;
v___x_469_ = lean_box(v___x_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
v___jp_471_:
{
uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = 2;
v___x_473_ = lean_box(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
v___jp_475_:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = 1;
v___x_477_ = lean_box(v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_460_ = stack[0].m_obj;
lean_object* v_args_461_ = stack[1].m_obj;
lean_object* v___y_462_ = stack[2].m_obj;
lean_object* v___y_463_ = stack[3].m_obj;
lean_object* v___y_464_ = stack[4].m_obj;
lean_object* v___y_465_ = stack[5].m_obj;
lean_object* v_res_525_;
v_res_525_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(v_ctor_460_, v_args_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object* v_ctor_526_, lean_object* v_args_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(v_ctor_526_, v_args_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_args_527_);
lean_dec_ref(v_ctor_526_);
return v_res_533_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___f_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0));
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_543_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_542_, v___f_541_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_543_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_535_ = stack[0].m_obj;
lean_object* v_a_536_ = stack[1].m_obj;
lean_object* v_a_537_ = stack[2].m_obj;
lean_object* v_a_538_ = stack[3].m_obj;
lean_object* v_a_539_ = stack[4].m_obj;
lean_object* v_res_544_;
v_res_544_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
stack->m_obj
 = v_res_544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___boxed(lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
return v_res_551_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(lean_object* v_00_u03b1_552_, lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_553_ = stack[1].m_obj;
lean_object* v___y_554_ = stack[2].m_obj;
lean_object* v___y_555_ = stack[3].m_obj;
lean_object* v___y_556_ = stack[4].m_obj;
lean_object* v___y_557_ = stack[5].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(lean_box(0), v_msg_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_561_, lean_object* v_msg_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(v_00_u03b1_561_, v_msg_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0));
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2);
return v___x_575_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object* v___x_577_, lean_object* v_ctor_578_, lean_object* v_args_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0));
v___x_787_ = lean_string_dec_eq(v_ctor_578_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = lean_array_get_size(v_args_579_);
v___x_790_ = lean_unsigned_to_nat(15u);
v___x_791_ = lean_nat_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v___x_792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_793_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_792_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
goto v___jp_585_;
}
}
v___jp_585_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_586_);
lean_inc(v___x_587_);
v___x_588_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_587_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_590_);
lean_inc(v___x_591_);
v___x_592_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_591_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = lean_unsigned_to_nat(2u);
v___x_595_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_594_);
lean_inc(v___x_595_);
v___x_596_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_595_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = lean_unsigned_to_nat(3u);
v___x_599_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_598_);
lean_inc(v___x_599_);
v___x_600_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_599_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = lean_unsigned_to_nat(4u);
v___x_603_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_602_);
lean_inc(v___x_603_);
v___x_604_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_603_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = lean_unsigned_to_nat(5u);
v___x_607_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_606_);
lean_inc(v___x_607_);
v___x_608_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_607_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_a_609_);
lean_dec_ref_known(v___x_608_, 1);
v___x_610_ = lean_unsigned_to_nat(6u);
v___x_611_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_610_);
lean_inc(v___x_611_);
v___x_612_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_611_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = lean_unsigned_to_nat(7u);
v___x_615_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_614_);
lean_inc(v___x_615_);
v___x_616_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_615_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = lean_unsigned_to_nat(8u);
v___x_619_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_618_);
lean_inc(v___x_619_);
v___x_620_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_619_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = lean_unsigned_to_nat(9u);
v___x_623_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_622_);
lean_inc(v___x_623_);
v___x_624_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_623_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_unsigned_to_nat(10u);
v___x_627_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_626_);
lean_inc(v___x_627_);
v___x_628_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_627_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = lean_unsigned_to_nat(11u);
v___x_631_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_630_);
lean_inc(v___x_631_);
v___x_632_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_631_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_unsigned_to_nat(12u);
v___x_635_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_634_);
lean_inc(v___x_635_);
v___x_636_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v___x_635_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = lean_unsigned_to_nat(13u);
v___x_639_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_638_);
lean_inc(v___x_639_);
v___x_640_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_639_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = lean_unsigned_to_nat(14u);
v___x_643_ = lean_array_get_borrowed(v___x_577_, v_args_579_, v___x_642_);
lean_inc(v___x_643_);
v___x_644_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_643_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_665_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_665_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_665_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_665_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; uint8_t v___x_650_; uint8_t v___x_651_; uint8_t v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; uint8_t v___x_657_; uint8_t v___x_658_; uint8_t v___x_659_; uint8_t v___x_660_; uint8_t v___x_661_; lean_object* v___x_663_; 
v___x_649_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v___x_649_, 0, v_a_589_);
lean_ctor_set(v___x_649_, 1, v_a_629_);
lean_ctor_set(v___x_649_, 2, v_a_645_);
v___x_650_ = lean_unbox(v_a_593_);
lean_dec(v_a_593_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3, v___x_650_);
v___x_651_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 1, v___x_651_);
v___x_652_ = lean_unbox(v_a_601_);
lean_dec(v_a_601_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 2, v___x_652_);
v___x_653_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 3, v___x_653_);
v___x_654_ = lean_unbox(v_a_609_);
lean_dec(v_a_609_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 4, v___x_654_);
v___x_655_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 5, v___x_655_);
v___x_656_ = lean_unbox(v_a_617_);
lean_dec(v_a_617_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 6, v___x_656_);
v___x_657_ = lean_unbox(v_a_621_);
lean_dec(v_a_621_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 7, v___x_657_);
v___x_658_ = lean_unbox(v_a_625_);
lean_dec(v_a_625_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 8, v___x_658_);
v___x_659_ = lean_unbox(v_a_633_);
lean_dec(v_a_633_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 9, v___x_659_);
v___x_660_ = lean_unbox(v_a_637_);
lean_dec(v_a_637_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 10, v___x_660_);
v___x_661_ = lean_unbox(v_a_641_);
lean_dec(v_a_641_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*3 + 11, v___x_661_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_663_ = v___x_647_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_649_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v_a_641_);
lean_dec(v_a_637_);
lean_dec(v_a_633_);
lean_dec(v_a_629_);
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
v_a_666_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_644_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_644_);
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
lean_dec(v_a_637_);
lean_dec(v_a_633_);
lean_dec(v_a_629_);
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
v_a_674_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_640_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_640_);
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
lean_dec(v_a_633_);
lean_dec(v_a_629_);
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
v_a_682_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_636_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_636_);
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
lean_dec(v_a_629_);
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
v_a_690_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_632_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_632_);
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
v_a_698_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_628_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_628_);
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
lean_dec(v_a_621_);
lean_dec(v_a_617_);
lean_dec(v_a_613_);
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_706_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_624_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_624_);
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
lean_dec(v_a_617_);
lean_dec(v_a_613_);
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_714_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_620_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_620_);
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
lean_dec(v_a_613_);
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_722_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_616_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_616_);
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
lean_dec(v_a_609_);
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_730_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_612_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_612_);
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
lean_dec(v_a_605_);
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_738_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_608_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_608_);
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
lean_dec(v_a_601_);
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_746_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_604_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_604_);
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
lean_dec(v_a_597_);
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_754_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_600_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_600_);
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
lean_dec(v_a_593_);
lean_dec(v_a_589_);
v_a_762_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_596_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_596_);
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
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_a_589_);
v_a_770_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_592_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_592_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_588_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_588_);
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
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_577_ = stack[0].m_obj;
lean_object* v_ctor_578_ = stack[1].m_obj;
lean_object* v_args_579_ = stack[2].m_obj;
lean_object* v___y_580_ = stack[3].m_obj;
lean_object* v___y_581_ = stack[4].m_obj;
lean_object* v___y_582_ = stack[5].m_obj;
lean_object* v___y_583_ = stack[6].m_obj;
lean_object* v_res_802_;
v_res_802_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(v___x_577_, v_ctor_578_, v_args_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_802_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object* v___x_803_, lean_object* v_ctor_804_, lean_object* v_args_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(v___x_803_, v_ctor_804_, v_args_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec_ref(v_args_805_);
lean_dec_ref(v_ctor_804_);
lean_dec_ref(v___x_803_);
return v_res_811_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_812_; lean_object* v___f_813_; 
v___x_812_ = l_Lean_instInhabitedExpr;
v___f_813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_813_, 0, v___x_812_);
return v___f_813_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___f_827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0);
v___x_828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_829_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_828_, v___f_827_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_829_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_821_ = stack[0].m_obj;
lean_object* v_a_822_ = stack[1].m_obj;
lean_object* v_a_823_ = stack[2].m_obj;
lean_object* v_a_824_ = stack[3].m_obj;
lean_object* v_a_825_ = stack[4].m_obj;
lean_object* v_res_830_;
v_res_830_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_box(0);
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_841_ = l_Lean_Expr_const___override(v___x_840_, v___x_839_);
return v___x_841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0));
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig(void){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_box(0);
v___x_849_ = l_Lean_Elab_abortTermExceptionId;
v___x_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_848_);
return v___x_850_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg(){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_854_;
v_res_854_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v_res_856_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_box(1);
v___x_858_ = l_Lean_MessageData_ofFormat(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2));
v___x_863_ = l_Lean_MessageData_ofFormat(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
return v_x_864_;
}
else
{
lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_889_; 
v_head_866_ = lean_ctor_get(v_x_865_, 0);
v_tail_867_ = lean_ctor_get(v_x_865_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_889_ == 0)
{
v___x_869_ = v_x_865_;
v_isShared_870_ = v_isSharedCheck_889_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_tail_867_);
lean_inc(v_head_866_);
lean_dec(v_x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_889_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_before_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_887_; 
v_before_871_ = lean_ctor_get(v_head_866_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_head_866_);
if (v_isSharedCheck_887_ == 0)
{
lean_object* v_unused_888_; 
v_unused_888_ = lean_ctor_get(v_head_866_, 1);
lean_dec(v_unused_888_);
v___x_873_ = v_head_866_;
v_isShared_874_ = v_isSharedCheck_887_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_before_871_);
lean_dec(v_head_866_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_887_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 7);
lean_ctor_set(v___x_873_, 1, v___x_875_);
lean_ctor_set(v___x_873_, 0, v_x_864_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_x_864_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_886_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3);
if (v_isShared_870_ == 0)
{
lean_ctor_set_tag(v___x_869_, 7);
lean_ctor_set(v___x_869_, 1, v___x_878_);
lean_ctor_set(v___x_869_, 0, v___x_877_);
v___x_880_ = v___x_869_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_885_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = l_Lean_MessageData_ofSyntax(v_before_871_);
v___x_882_ = l_Lean_indentD(v___x_881_);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_880_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v_x_864_ = v___x_883_;
v_x_865_ = v_tail_867_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object* v_opts_890_, lean_object* v_opt_891_){
_start:
{
lean_object* v_name_892_; lean_object* v_defValue_893_; lean_object* v_map_894_; lean_object* v___x_895_; 
v_name_892_ = lean_ctor_get(v_opt_891_, 0);
v_defValue_893_ = lean_ctor_get(v_opt_891_, 1);
v_map_894_ = lean_ctor_get(v_opts_890_, 0);
v___x_895_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_894_, v_name_892_);
if (lean_obj_tag(v___x_895_) == 0)
{
uint8_t v___x_896_; 
v___x_896_ = lean_unbox(v_defValue_893_);
return v___x_896_;
}
else
{
lean_object* v_val_897_; 
v_val_897_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_895_, 1);
if (lean_obj_tag(v_val_897_) == 1)
{
uint8_t v_v_898_; 
v_v_898_ = lean_ctor_get_uint8(v_val_897_, 0);
lean_dec_ref_known(v_val_897_, 0);
return v_v_898_;
}
else
{
uint8_t v___x_899_; 
lean_dec(v_val_897_);
v___x_899_ = lean_unbox(v_defValue_893_);
return v___x_899_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_890_ = stack[0].m_obj;
lean_object* v_opt_891_ = stack[1].m_obj;
uint8_t v_res_900_;
v_res_900_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_opts_890_, v_opt_891_);
stack->m_num = v_res_900_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object* v_opts_901_, lean_object* v_opt_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_opts_901_, v_opt_902_);
lean_dec_ref(v_opt_902_);
lean_dec_ref(v_opts_901_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1));
v___x_909_ = l_Lean_MessageData_ofFormat(v___x_908_);
return v___x_909_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object* v_msgData_910_, lean_object* v_macroStack_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_914_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_912_);
v___x_915_ = l_Lean_Elab_pp_macroStack;
v___x_916_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v___x_914_, v___x_915_);
lean_dec_ref(v___x_914_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec(v_macroStack_911_);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v_msgData_910_);
return v___x_917_;
}
else
{
if (lean_obj_tag(v_macroStack_911_) == 0)
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v_msgData_910_);
return v___x_918_;
}
else
{
lean_object* v_head_919_; lean_object* v_after_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_935_; 
v_head_919_ = lean_ctor_get(v_macroStack_911_, 0);
lean_inc(v_head_919_);
v_after_920_ = lean_ctor_get(v_head_919_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_head_919_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_head_919_, 0);
lean_dec(v_unused_936_);
v___x_922_ = v_head_919_;
v_isShared_923_ = v_isSharedCheck_935_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_after_920_);
lean_dec(v_head_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_935_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 7);
lean_ctor_set(v___x_922_, 1, v___x_924_);
lean_ctor_set(v___x_922_, 0, v_msgData_910_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_msgData_910_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_934_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_msgData_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_927_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_MessageData_ofSyntax(v_after_920_);
v___x_930_ = l_Lean_indentD(v___x_929_);
v_msgData_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_931_, 0, v___x_928_);
lean_ctor_set(v_msgData_931_, 1, v___x_930_);
v___x_932_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(v_msgData_931_, v_macroStack_911_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_910_ = stack[0].m_obj;
lean_object* v_macroStack_911_ = stack[1].m_obj;
lean_object* v___y_912_ = stack[2].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_910_, v_macroStack_911_, v___y_912_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_msgData_938_, lean_object* v_macroStack_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_938_, v_macroStack_939_, v___y_940_);
lean_dec_ref(v___y_940_);
return v_res_942_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object* v_msg_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_ref_951_; lean_object* v_macroStack_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_ref_951_ = lean_ctor_get(v___y_948_, 2);
v_macroStack_952_ = lean_ctor_get(v___y_944_, 1);
v___x_953_ = l_Lean_Elab_getBetterRef(v_ref_951_, v_macroStack_952_);
v___x_954_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_943_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref(v___x_954_);
lean_inc(v_macroStack_952_);
v___x_956_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_a_955_, v_macroStack_952_, v___y_948_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_965_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_953_);
lean_ctor_set(v___x_961_, 1, v_a_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_943_ = stack[0].m_obj;
lean_object* v___y_944_ = stack[1].m_obj;
lean_object* v___y_945_ = stack[2].m_obj;
lean_object* v___y_946_ = stack[3].m_obj;
lean_object* v___y_947_ = stack[4].m_obj;
lean_object* v___y_948_ = stack[5].m_obj;
lean_object* v___y_949_ = stack[6].m_obj;
lean_object* v_res_966_;
v_res_966_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
stack->m_obj
 = v_res_966_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_975_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object* v_e_976_, lean_object* v___y_977_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = l_Lean_Expr_hasMVar(v_e_976_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_e_976_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v_mctx_982_; lean_object* v___x_983_; lean_object* v_fst_984_; lean_object* v_snd_985_; lean_object* v___x_986_; lean_object* v_cache_987_; lean_object* v_zetaDeltaFVarIds_988_; lean_object* v_postponed_989_; lean_object* v_diag_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_999_; 
v___x_981_ = lean_st_ref_get(v___y_977_);
v_mctx_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_ref(v_mctx_982_);
lean_dec(v___x_981_);
v___x_983_ = l_Lean_instantiateMVarsCore(v_mctx_982_, v_e_976_);
v_fst_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_fst_984_);
v_snd_985_ = lean_ctor_get(v___x_983_, 1);
lean_inc(v_snd_985_);
lean_dec_ref(v___x_983_);
v___x_986_ = lean_st_ref_take(v___y_977_);
v_cache_987_ = lean_ctor_get(v___x_986_, 1);
v_zetaDeltaFVarIds_988_ = lean_ctor_get(v___x_986_, 2);
v_postponed_989_ = lean_ctor_get(v___x_986_, 3);
v_diag_990_ = lean_ctor_get(v___x_986_, 4);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v___x_986_, 0);
lean_dec(v_unused_1000_);
v___x_992_ = v___x_986_;
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_diag_990_);
lean_inc(v_postponed_989_);
lean_inc(v_zetaDeltaFVarIds_988_);
lean_inc(v_cache_987_);
lean_dec(v___x_986_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v_snd_985_);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_snd_985_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_cache_987_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_zetaDeltaFVarIds_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_postponed_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_diag_990_);
v___x_995_ = v_reuseFailAlloc_998_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_st_ref_put(v___y_977_, v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_fst_984_);
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_976_ = stack[0].m_obj;
lean_object* v___y_977_ = stack[1].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_976_, v___y_977_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object* v_e_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_1002_, v___y_1003_);
lean_dec(v___y_1003_);
return v_res_1005_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_1010_ = l_Lean_MessageData_ofExpr(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2);
v___x_1012_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___x_1011_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1018_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(lean_object* v_stx_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_ty_x3f_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_toCold_1040_; lean_object* v_currRecDepth_1041_; lean_object* v_ref_1042_; uint16_t v_optionFlags_1043_; uint8_t v_suppressElabErrors_1044_; uint8_t v_isRecordingDeps_1045_; uint8_t v___x_1046_; lean_object* v_ref_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_ty_x3f_1034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_1035_ = 1;
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_box(v___x_1035_);
v___x_1038_ = lean_box(v___x_1035_);
lean_inc(v_stx_1026_);
v___x_1039_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1039_, 0, v_stx_1026_);
lean_closure_set(v___x_1039_, 1, v_ty_x3f_1034_);
lean_closure_set(v___x_1039_, 2, v___x_1037_);
lean_closure_set(v___x_1039_, 3, v___x_1038_);
lean_closure_set(v___x_1039_, 4, v___x_1036_);
v_toCold_1040_ = lean_ctor_get(v_a_1031_, 0);
v_currRecDepth_1041_ = lean_ctor_get(v_a_1031_, 1);
v_ref_1042_ = lean_ctor_get(v_a_1031_, 2);
v_optionFlags_1043_ = lean_ctor_get_uint16(v_a_1031_, sizeof(void*)*3);
v_suppressElabErrors_1044_ = lean_ctor_get_uint8(v_a_1031_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1045_ = lean_ctor_get_uint8(v_a_1031_, sizeof(void*)*3 + 3);
v___x_1046_ = 1;
v_ref_1047_ = l_Lean_replaceRef(v_stx_1026_, v_ref_1042_);
lean_dec(v_stx_1026_);
lean_inc(v_currRecDepth_1041_);
lean_inc_ref(v_toCold_1040_);
v___x_1048_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1048_, 0, v_toCold_1040_);
lean_ctor_set(v___x_1048_, 1, v_currRecDepth_1041_);
lean_ctor_set(v___x_1048_, 2, v_ref_1047_);
lean_ctor_set_uint16(v___x_1048_, sizeof(void*)*3, v_optionFlags_1043_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*3 + 2, v_suppressElabErrors_1044_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*3 + 3, v_isRecordingDeps_1045_);
v___x_1049_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1039_, v___x_1046_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v___x_1048_, v_a_1032_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v_a_1052_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; uint8_t v___x_1147_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1050_, v_a_1030_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref(v___x_1051_);
v___x_1147_ = l_Lean_Expr_hasSorry(v_a_1052_);
if (v___x_1147_ == 0)
{
v___y_1092_ = v_a_1027_;
v___y_1093_ = v_a_1028_;
v___y_1094_ = v_a_1029_;
v___y_1095_ = v_a_1030_;
v___y_1096_ = v___x_1048_;
v___y_1097_ = v_a_1032_;
goto v___jp_1091_;
}
else
{
uint8_t v___x_1148_; 
v___x_1148_ = l_Lean_Expr_hasSyntheticSorry(v_a_1052_);
if (v___x_1148_ == 0)
{
v___y_1129_ = v_a_1027_;
v___y_1130_ = v_a_1028_;
v___y_1131_ = v_a_1029_;
v___y_1132_ = v_a_1030_;
v___y_1133_ = v___x_1048_;
v___y_1134_ = v_a_1032_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1052_);
lean_dec_ref_known(v___x_1048_, 3);
v___x_1149_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
v___jp_1053_:
{
if (v___y_1063_ == 0)
{
if (lean_obj_tag(v___y_1060_) == 0)
{
lean_dec_ref_known(v___y_1060_, 2);
lean_dec_ref(v___y_1061_);
lean_dec(v_a_1052_);
return v___y_1057_;
}
else
{
lean_object* v_id_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1077_; 
v_id_1064_ = lean_ctor_get(v___y_1060_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___y_1060_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___y_1060_, 1);
lean_dec(v_unused_1078_);
v___x_1066_ = v___y_1060_;
v_isShared_1067_ = v_isSharedCheck_1077_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_id_1064_);
lean_dec(v___y_1060_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1077_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1054_, v_id_1064_);
lean_dec(v_id_1064_);
if (v___x_1068_ == 0)
{
lean_del_object(v___x_1066_);
lean_dec_ref(v___y_1061_);
lean_dec(v_a_1052_);
return v___y_1057_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_dec_ref(v___y_1057_);
v___x_1069_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6);
v___x_1070_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1071_ = l_Lean_indentExpr(v_a_1052_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 7);
lean_ctor_set(v___x_1066_, 1, v___x_1071_);
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1073_ = v___x_1066_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1069_);
v___x_1075_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1074_, v___y_1058_, v___y_1056_, v___y_1055_, v___y_1062_, v___y_1061_, v___y_1059_);
lean_dec_ref(v___y_1061_);
return v___x_1075_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v_a_1052_);
return v___y_1057_;
}
}
v___jp_1079_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1052_);
v___x_1087_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_1052_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_dec_ref(v___y_1084_);
lean_dec(v_a_1052_);
return v___x_1087_;
}
else
{
lean_object* v_a_1088_; uint8_t v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
v___x_1089_ = l_Lean_Exception_isInterrupt(v_a_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
lean_inc(v_a_1088_);
v___x_1090_ = l_Lean_Exception_isRuntime(v_a_1088_);
v___y_1054_ = v___x_1086_;
v___y_1055_ = v___y_1082_;
v___y_1056_ = v___y_1081_;
v___y_1057_ = v___x_1087_;
v___y_1058_ = v___y_1080_;
v___y_1059_ = v___y_1085_;
v___y_1060_ = v_a_1088_;
v___y_1061_ = v___y_1084_;
v___y_1062_ = v___y_1083_;
v___y_1063_ = v___x_1090_;
goto v___jp_1053_;
}
else
{
v___y_1054_ = v___x_1086_;
v___y_1055_ = v___y_1082_;
v___y_1056_ = v___y_1081_;
v___y_1057_ = v___x_1087_;
v___y_1058_ = v___y_1080_;
v___y_1059_ = v___y_1085_;
v___y_1060_ = v_a_1088_;
v___y_1061_ = v___y_1084_;
v___y_1062_ = v___y_1083_;
v___y_1063_ = v___x_1089_;
goto v___jp_1053_;
}
}
}
v___jp_1091_:
{
lean_object* v___x_1098_; 
lean_inc(v_a_1052_);
v___x_1098_ = l_Lean_Meta_getMVars(v_a_1052_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1099_, v___x_1036_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v_a_1099_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; uint8_t v___x_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = lean_unbox(v_a_1101_);
lean_dec(v_a_1101_);
if (v___x_1102_ == 0)
{
v___y_1080_ = v___y_1092_;
v___y_1081_ = v___y_1093_;
v___y_1082_ = v___y_1094_;
v___y_1083_ = v___y_1095_;
v___y_1084_ = v___y_1096_;
v___y_1085_ = v___y_1097_;
goto v___jp_1079_;
}
else
{
lean_object* v___x_1103_; lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v___y_1096_);
lean_dec(v_a_1052_);
v___x_1103_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v___y_1096_);
lean_dec(v_a_1052_);
v_a_1112_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1100_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1100_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___y_1096_);
lean_dec(v_a_1052_);
v_a_1120_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1098_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1098_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
v___jp_1128_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v___x_1135_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1136_ = l_Lean_indentExpr(v_a_1052_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1137_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec_ref(v___y_1133_);
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
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref_known(v___x_1048_, 3);
v_a_1158_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1049_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1049_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1026_ = stack[0].m_obj;
lean_object* v_a_1027_ = stack[1].m_obj;
lean_object* v_a_1028_ = stack[2].m_obj;
lean_object* v_a_1029_ = stack[3].m_obj;
lean_object* v_a_1030_ = stack[4].m_obj;
lean_object* v_a_1031_ = stack[5].m_obj;
lean_object* v_a_1032_ = stack[6].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_stx_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_stx_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
return v_res_1175_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_1177_ = l_Lean_MessageData_ofExpr(v___x_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0);
v___x_1179_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1182_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v___x_1181_);
return v___x_1183_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_ty_x3f_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v_toCold_1198_; lean_object* v_currRecDepth_1199_; lean_object* v_ref_1200_; uint16_t v_optionFlags_1201_; uint8_t v_suppressElabErrors_1202_; uint8_t v_isRecordingDeps_1203_; uint8_t v___x_1204_; lean_object* v_ref_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_ty_x3f_1192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_1193_ = 1;
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_box(v___x_1193_);
v___x_1196_ = lean_box(v___x_1193_);
lean_inc(v_stx_1184_);
v___x_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1197_, 0, v_stx_1184_);
lean_closure_set(v___x_1197_, 1, v_ty_x3f_1192_);
lean_closure_set(v___x_1197_, 2, v___x_1195_);
lean_closure_set(v___x_1197_, 3, v___x_1196_);
lean_closure_set(v___x_1197_, 4, v___x_1194_);
v_toCold_1198_ = lean_ctor_get(v_a_1189_, 0);
v_currRecDepth_1199_ = lean_ctor_get(v_a_1189_, 1);
v_ref_1200_ = lean_ctor_get(v_a_1189_, 2);
v_optionFlags_1201_ = lean_ctor_get_uint16(v_a_1189_, sizeof(void*)*3);
v_suppressElabErrors_1202_ = lean_ctor_get_uint8(v_a_1189_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1203_ = lean_ctor_get_uint8(v_a_1189_, sizeof(void*)*3 + 3);
v___x_1204_ = 1;
v_ref_1205_ = l_Lean_replaceRef(v_stx_1184_, v_ref_1200_);
lean_dec(v_stx_1184_);
lean_inc(v_currRecDepth_1199_);
lean_inc_ref(v_toCold_1198_);
v___x_1206_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1206_, 0, v_toCold_1198_);
lean_ctor_set(v___x_1206_, 1, v_currRecDepth_1199_);
lean_ctor_set(v___x_1206_, 2, v_ref_1205_);
lean_ctor_set_uint16(v___x_1206_, sizeof(void*)*3, v_optionFlags_1201_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*3 + 2, v_suppressElabErrors_1202_);
lean_ctor_set_uint8(v___x_1206_, sizeof(void*)*3 + 3, v_isRecordingDeps_1203_);
v___x_1207_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1197_, v___x_1204_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v___x_1206_, v_a_1190_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; uint8_t v___x_1305_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1207_, 1);
v___x_1209_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1208_, v_a_1188_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
v___x_1305_ = l_Lean_Expr_hasSorry(v_a_1210_);
if (v___x_1305_ == 0)
{
v___y_1250_ = v_a_1185_;
v___y_1251_ = v_a_1186_;
v___y_1252_ = v_a_1187_;
v___y_1253_ = v_a_1188_;
v___y_1254_ = v___x_1206_;
v___y_1255_ = v_a_1190_;
goto v___jp_1249_;
}
else
{
uint8_t v___x_1306_; 
v___x_1306_ = l_Lean_Expr_hasSyntheticSorry(v_a_1210_);
if (v___x_1306_ == 0)
{
v___y_1287_ = v_a_1185_;
v___y_1288_ = v_a_1186_;
v___y_1289_ = v_a_1187_;
v___y_1290_ = v_a_1188_;
v___y_1291_ = v___x_1206_;
v___y_1292_ = v_a_1190_;
goto v___jp_1286_;
}
else
{
lean_object* v___x_1307_; lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_a_1210_);
lean_dec_ref_known(v___x_1206_, 3);
v___x_1307_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
v___jp_1211_:
{
if (v___y_1221_ == 0)
{
if (lean_obj_tag(v___y_1213_) == 0)
{
lean_dec_ref_known(v___y_1213_, 2);
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1210_);
return v___y_1220_;
}
else
{
lean_object* v_id_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1235_; 
v_id_1222_ = lean_ctor_get(v___y_1213_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___y_1213_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___y_1213_, 1);
lean_dec(v_unused_1236_);
v___x_1224_ = v___y_1213_;
v_isShared_1225_ = v_isSharedCheck_1235_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_id_1222_);
lean_dec(v___y_1213_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1235_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
uint8_t v___x_1226_; 
v___x_1226_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1216_, v_id_1222_);
lean_dec(v_id_1222_);
if (v___x_1226_ == 0)
{
lean_del_object(v___x_1224_);
lean_dec_ref(v___y_1219_);
lean_dec(v_a_1210_);
return v___y_1220_;
}
else
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_dec_ref(v___y_1220_);
v___x_1227_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_1228_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1229_ = l_Lean_indentExpr(v_a_1210_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 7);
lean_ctor_set(v___x_1224_, 1, v___x_1229_);
lean_ctor_set(v___x_1224_, 0, v___x_1228_);
v___x_1231_ = v___x_1224_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v___x_1227_);
v___x_1233_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1232_, v___y_1218_, v___y_1215_, v___y_1217_, v___y_1214_, v___y_1219_, v___y_1212_);
lean_dec_ref(v___y_1219_);
return v___x_1233_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1219_);
lean_dec_ref(v___y_1213_);
lean_dec(v_a_1210_);
return v___y_1220_;
}
}
v___jp_1237_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1210_);
v___x_1245_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_1210_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_dec_ref(v___y_1242_);
lean_dec(v_a_1210_);
return v___x_1245_;
}
else
{
lean_object* v_a_1246_; uint8_t v___x_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
v___x_1247_ = l_Lean_Exception_isInterrupt(v_a_1246_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
lean_inc(v_a_1246_);
v___x_1248_ = l_Lean_Exception_isRuntime(v_a_1246_);
v___y_1212_ = v___y_1243_;
v___y_1213_ = v_a_1246_;
v___y_1214_ = v___y_1241_;
v___y_1215_ = v___y_1239_;
v___y_1216_ = v___x_1244_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___y_1238_;
v___y_1219_ = v___y_1242_;
v___y_1220_ = v___x_1245_;
v___y_1221_ = v___x_1248_;
goto v___jp_1211_;
}
else
{
v___y_1212_ = v___y_1243_;
v___y_1213_ = v_a_1246_;
v___y_1214_ = v___y_1241_;
v___y_1215_ = v___y_1239_;
v___y_1216_ = v___x_1244_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___y_1238_;
v___y_1219_ = v___y_1242_;
v___y_1220_ = v___x_1245_;
v___y_1221_ = v___x_1247_;
goto v___jp_1211_;
}
}
}
v___jp_1249_:
{
lean_object* v___x_1256_; 
lean_inc(v_a_1210_);
v___x_1256_ = l_Lean_Meta_getMVars(v_a_1210_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1257_, v___x_1194_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v_a_1257_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; uint8_t v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v___x_1260_ = lean_unbox(v_a_1259_);
lean_dec(v_a_1259_);
if (v___x_1260_ == 0)
{
v___y_1238_ = v___y_1250_;
v___y_1239_ = v___y_1251_;
v___y_1240_ = v___y_1252_;
v___y_1241_ = v___y_1253_;
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___y_1255_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___y_1254_);
lean_dec(v_a_1210_);
v___x_1261_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
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
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v___y_1254_);
lean_dec(v_a_1210_);
v_a_1270_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1258_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1258_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v___y_1254_);
lean_dec(v_a_1210_);
v_a_1278_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1256_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1256_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
v___jp_1286_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v___x_1293_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1294_ = l_Lean_indentExpr(v_a_1210_);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1295_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec_ref(v___y_1291_);
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref_known(v___x_1206_, 3);
v_a_1316_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1207_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1207_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1184_ = stack[0].m_obj;
lean_object* v_a_1185_ = stack[1].m_obj;
lean_object* v_a_1186_ = stack[2].m_obj;
lean_object* v_a_1187_ = stack[3].m_obj;
lean_object* v_a_1188_ = stack[4].m_obj;
lean_object* v_a_1189_ = stack[5].m_obj;
lean_object* v_a_1190_ = stack[6].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
return v_res_1333_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(lean_object* v_stx_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_toCold_1342_; lean_object* v_currRecDepth_1343_; lean_object* v_ref_1344_; uint16_t v_optionFlags_1345_; uint8_t v_suppressElabErrors_1346_; uint8_t v_isRecordingDeps_1347_; lean_object* v___x_1348_; lean_object* v_ref_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_toCold_1342_ = lean_ctor_get(v_a_1339_, 0);
v_currRecDepth_1343_ = lean_ctor_get(v_a_1339_, 1);
v_ref_1344_ = lean_ctor_get(v_a_1339_, 2);
v_optionFlags_1345_ = lean_ctor_get_uint16(v_a_1339_, sizeof(void*)*3);
v_suppressElabErrors_1346_ = lean_ctor_get_uint8(v_a_1339_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1347_ = lean_ctor_get_uint8(v_a_1339_, sizeof(void*)*3 + 3);
v___x_1348_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1349_ = l_Lean_replaceRef(v_stx_1334_, v_ref_1344_);
lean_inc(v_currRecDepth_1343_);
lean_inc_ref(v_toCold_1342_);
v___x_1350_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1350_, 0, v_toCold_1342_);
lean_ctor_set(v___x_1350_, 1, v_currRecDepth_1343_);
lean_ctor_set(v___x_1350_, 2, v_ref_1349_);
lean_ctor_set_uint16(v___x_1350_, sizeof(void*)*3, v_optionFlags_1345_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*3 + 2, v_suppressElabErrors_1346_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*3 + 3, v_isRecordingDeps_1347_);
lean_inc(v_stx_1334_);
v___x_1351_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_stx_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v___x_1350_, v_a_1340_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref_known(v___x_1350_, 3);
lean_dec(v_stx_1334_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_fst_1356_; lean_object* v___x_1358_; 
v_fst_1356_ = lean_ctor_get(v_a_1352_, 0);
lean_inc(v_fst_1356_);
lean_dec(v_a_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_fst_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_fst_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1375_; 
v_a_1361_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1363_ = v___x_1351_;
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1351_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1375_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
lean_inc(v_a_1361_);
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
uint8_t v___y_1368_; uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_Exception_isInterrupt(v_a_1361_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; 
lean_inc(v_a_1361_);
v___x_1373_ = l_Lean_Exception_isRuntime(v_a_1361_);
v___y_1368_ = v___x_1373_;
goto v___jp_1367_;
}
else
{
v___y_1368_ = v___x_1372_;
goto v___jp_1367_;
}
v___jp_1367_:
{
if (v___y_1368_ == 0)
{
if (lean_obj_tag(v_a_1361_) == 0)
{
lean_dec_ref_known(v_a_1361_, 2);
lean_dec_ref_known(v___x_1350_, 3);
lean_dec(v_stx_1334_);
return v___x_1366_;
}
else
{
lean_object* v_id_1369_; uint8_t v___x_1370_; 
v_id_1369_ = lean_ctor_get(v_a_1361_, 0);
lean_inc(v_id_1369_);
lean_dec_ref_known(v_a_1361_, 2);
v___x_1370_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1348_, v_id_1369_);
lean_dec(v_id_1369_);
if (v___x_1370_ == 0)
{
lean_dec_ref_known(v___x_1350_, 3);
lean_dec(v_stx_1334_);
return v___x_1366_;
}
else
{
lean_object* v___x_1371_; 
lean_dec_ref(v___x_1366_);
v___x_1371_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v___x_1350_, v_a_1340_);
lean_dec_ref_known(v___x_1350_, 3);
return v___x_1371_;
}
}
}
else
{
lean_dec(v_a_1361_);
lean_dec_ref_known(v___x_1350_, 3);
lean_dec(v_stx_1334_);
return v___x_1366_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1334_ = stack[0].m_obj;
lean_object* v_a_1335_ = stack[1].m_obj;
lean_object* v_a_1336_ = stack[2].m_obj;
lean_object* v_a_1337_ = stack[3].m_obj;
lean_object* v_a_1338_ = stack[4].m_obj;
lean_object* v_a_1339_ = stack[5].m_obj;
lean_object* v_a_1340_ = stack[6].m_obj;
lean_object* v_res_1376_;
v_res_1376_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_stx_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
stack->m_obj
 = v_res_1376_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_stx_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
return v_res_1385_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_1391_ = l_Lean_mkConst(v___x_1390_, v___x_1389_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1392_; lean_object* v_ty_x3f_1393_; 
v___x_1392_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_1393_, 0, v___x_1392_);
return v_ty_x3f_1393_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_1395_ = l_Lean_MessageData_ofExpr(v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_1397_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___x_1396_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1400_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v___x_1399_);
return v___x_1401_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_ty_x3f_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_toCold_1416_; lean_object* v_currRecDepth_1417_; lean_object* v_ref_1418_; uint16_t v_optionFlags_1419_; uint8_t v_suppressElabErrors_1420_; uint8_t v_isRecordingDeps_1421_; uint8_t v___x_1422_; lean_object* v_ref_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_ty_x3f_1410_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_1411_ = 1;
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_box(v___x_1411_);
v___x_1414_ = lean_box(v___x_1411_);
lean_inc(v_stx_1402_);
v___x_1415_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1415_, 0, v_stx_1402_);
lean_closure_set(v___x_1415_, 1, v_ty_x3f_1410_);
lean_closure_set(v___x_1415_, 2, v___x_1413_);
lean_closure_set(v___x_1415_, 3, v___x_1414_);
lean_closure_set(v___x_1415_, 4, v___x_1412_);
v_toCold_1416_ = lean_ctor_get(v_a_1407_, 0);
v_currRecDepth_1417_ = lean_ctor_get(v_a_1407_, 1);
v_ref_1418_ = lean_ctor_get(v_a_1407_, 2);
v_optionFlags_1419_ = lean_ctor_get_uint16(v_a_1407_, sizeof(void*)*3);
v_suppressElabErrors_1420_ = lean_ctor_get_uint8(v_a_1407_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1421_ = lean_ctor_get_uint8(v_a_1407_, sizeof(void*)*3 + 3);
v___x_1422_ = 1;
v_ref_1423_ = l_Lean_replaceRef(v_stx_1402_, v_ref_1418_);
lean_dec(v_stx_1402_);
lean_inc(v_currRecDepth_1417_);
lean_inc_ref(v_toCold_1416_);
v___x_1424_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1424_, 0, v_toCold_1416_);
lean_ctor_set(v___x_1424_, 1, v_currRecDepth_1417_);
lean_ctor_set(v___x_1424_, 2, v_ref_1423_);
lean_ctor_set_uint16(v___x_1424_, sizeof(void*)*3, v_optionFlags_1419_);
lean_ctor_set_uint8(v___x_1424_, sizeof(void*)*3 + 2, v_suppressElabErrors_1420_);
lean_ctor_set_uint8(v___x_1424_, sizeof(void*)*3 + 3, v_isRecordingDeps_1421_);
v___x_1425_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1415_, v___x_1422_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v___x_1424_, v_a_1408_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v_a_1428_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; uint8_t v___y_1439_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; uint8_t v___x_1523_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1426_, v_a_1406_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1523_ = l_Lean_Expr_hasSorry(v_a_1428_);
if (v___x_1523_ == 0)
{
v___y_1468_ = v_a_1403_;
v___y_1469_ = v_a_1404_;
v___y_1470_ = v_a_1405_;
v___y_1471_ = v_a_1406_;
v___y_1472_ = v___x_1424_;
v___y_1473_ = v_a_1408_;
goto v___jp_1467_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_Expr_hasSyntheticSorry(v_a_1428_);
if (v___x_1524_ == 0)
{
v___y_1505_ = v_a_1403_;
v___y_1506_ = v_a_1404_;
v___y_1507_ = v_a_1405_;
v___y_1508_ = v_a_1406_;
v___y_1509_ = v___x_1424_;
v___y_1510_ = v_a_1408_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1525_; lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec(v_a_1428_);
lean_dec_ref_known(v___x_1424_, 3);
v___x_1525_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
v___jp_1429_:
{
if (v___y_1439_ == 0)
{
if (lean_obj_tag(v___y_1437_) == 0)
{
lean_dec_ref_known(v___y_1437_, 2);
lean_dec_ref(v___y_1431_);
lean_dec(v_a_1428_);
return v___y_1435_;
}
else
{
lean_object* v_id_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1453_; 
v_id_1440_ = lean_ctor_get(v___y_1437_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___y_1437_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___y_1437_, 1);
lean_dec(v_unused_1454_);
v___x_1442_ = v___y_1437_;
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_id_1440_);
lean_dec(v___y_1437_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1453_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
uint8_t v___x_1444_; 
v___x_1444_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1438_, v_id_1440_);
lean_dec(v_id_1440_);
if (v___x_1444_ == 0)
{
lean_del_object(v___x_1442_);
lean_dec_ref(v___y_1431_);
lean_dec(v_a_1428_);
return v___y_1435_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_dec_ref(v___y_1435_);
v___x_1445_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_1446_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1447_ = l_Lean_indentExpr(v_a_1428_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 7);
lean_ctor_set(v___x_1442_, 1, v___x_1447_);
lean_ctor_set(v___x_1442_, 0, v___x_1446_);
v___x_1449_ = v___x_1442_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v___x_1445_);
v___x_1451_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1450_, v___y_1436_, v___y_1432_, v___y_1434_, v___y_1430_, v___y_1431_, v___y_1433_);
lean_dec_ref(v___y_1431_);
return v___x_1451_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1437_);
lean_dec_ref(v___y_1431_);
lean_dec(v_a_1428_);
return v___y_1435_;
}
}
v___jp_1455_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1428_);
v___x_1463_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_a_1428_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec_ref(v___y_1460_);
lean_dec(v_a_1428_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; uint8_t v___x_1465_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
v___x_1465_ = l_Lean_Exception_isInterrupt(v_a_1464_);
if (v___x_1465_ == 0)
{
uint8_t v___x_1466_; 
lean_inc(v_a_1464_);
v___x_1466_ = l_Lean_Exception_isRuntime(v_a_1464_);
v___y_1430_ = v___y_1459_;
v___y_1431_ = v___y_1460_;
v___y_1432_ = v___y_1457_;
v___y_1433_ = v___y_1461_;
v___y_1434_ = v___y_1458_;
v___y_1435_ = v___x_1463_;
v___y_1436_ = v___y_1456_;
v___y_1437_ = v_a_1464_;
v___y_1438_ = v___x_1462_;
v___y_1439_ = v___x_1466_;
goto v___jp_1429_;
}
else
{
v___y_1430_ = v___y_1459_;
v___y_1431_ = v___y_1460_;
v___y_1432_ = v___y_1457_;
v___y_1433_ = v___y_1461_;
v___y_1434_ = v___y_1458_;
v___y_1435_ = v___x_1463_;
v___y_1436_ = v___y_1456_;
v___y_1437_ = v_a_1464_;
v___y_1438_ = v___x_1462_;
v___y_1439_ = v___x_1465_;
goto v___jp_1429_;
}
}
}
v___jp_1467_:
{
lean_object* v___x_1474_; 
lean_inc(v_a_1428_);
v___x_1474_ = l_Lean_Meta_getMVars(v_a_1428_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1475_, v___x_1412_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v_a_1475_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; uint8_t v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1478_ = lean_unbox(v_a_1477_);
lean_dec(v_a_1477_);
if (v___x_1478_ == 0)
{
v___y_1456_ = v___y_1468_;
v___y_1457_ = v___y_1469_;
v___y_1458_ = v___y_1470_;
v___y_1459_ = v___y_1471_;
v___y_1460_ = v___y_1472_;
v___y_1461_ = v___y_1473_;
goto v___jp_1455_;
}
else
{
lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___y_1472_);
lean_dec(v_a_1428_);
v___x_1479_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v___y_1472_);
lean_dec(v_a_1428_);
v_a_1488_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1476_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1476_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
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
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec_ref(v___y_1472_);
lean_dec(v_a_1428_);
v_a_1496_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1474_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1474_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
v___jp_1504_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
v___x_1511_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1512_ = l_Lean_indentExpr(v_a_1428_);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1513_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec_ref(v___y_1509_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
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
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref_known(v___x_1424_, 3);
v_a_1534_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1425_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1425_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
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
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1402_ = stack[0].m_obj;
lean_object* v_a_1403_ = stack[1].m_obj;
lean_object* v_a_1404_ = stack[2].m_obj;
lean_object* v_a_1405_ = stack[3].m_obj;
lean_object* v_a_1406_ = stack[4].m_obj;
lean_object* v_a_1407_ = stack[5].m_obj;
lean_object* v_a_1408_ = stack[6].m_obj;
lean_object* v_res_1542_;
v_res_1542_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
stack->m_obj
 = v_res_1542_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
return v_res_1551_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_toCold_1560_; lean_object* v_currRecDepth_1561_; lean_object* v_ref_1562_; uint16_t v_optionFlags_1563_; uint8_t v_suppressElabErrors_1564_; uint8_t v_isRecordingDeps_1565_; lean_object* v___x_1566_; lean_object* v_ref_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_toCold_1560_ = lean_ctor_get(v_a_1557_, 0);
v_currRecDepth_1561_ = lean_ctor_get(v_a_1557_, 1);
v_ref_1562_ = lean_ctor_get(v_a_1557_, 2);
v_optionFlags_1563_ = lean_ctor_get_uint16(v_a_1557_, sizeof(void*)*3);
v_suppressElabErrors_1564_ = lean_ctor_get_uint8(v_a_1557_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1565_ = lean_ctor_get_uint8(v_a_1557_, sizeof(void*)*3 + 3);
v___x_1566_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1567_ = l_Lean_replaceRef(v_stx_1552_, v_ref_1562_);
lean_inc(v_currRecDepth_1561_);
lean_inc_ref(v_toCold_1560_);
v___x_1568_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1568_, 0, v_toCold_1560_);
lean_ctor_set(v___x_1568_, 1, v_currRecDepth_1561_);
lean_ctor_set(v___x_1568_, 2, v_ref_1567_);
lean_ctor_set_uint16(v___x_1568_, sizeof(void*)*3, v_optionFlags_1563_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*3 + 2, v_suppressElabErrors_1564_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*3 + 3, v_isRecordingDeps_1565_);
lean_inc(v_stx_1552_);
v___x_1569_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v___x_1568_, v_a_1558_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref_known(v___x_1568_, 3);
lean_dec(v_stx_1552_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_fst_1574_; lean_object* v___x_1576_; 
v_fst_1574_ = lean_ctor_get(v_a_1570_, 0);
lean_inc(v_fst_1574_);
lean_dec(v_a_1570_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_fst_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_fst_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1593_; 
v_a_1579_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1581_ = v___x_1569_;
v_isShared_1582_ = v_isSharedCheck_1593_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1569_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1593_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
lean_inc(v_a_1579_);
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
uint8_t v___y_1586_; uint8_t v___x_1590_; 
v___x_1590_ = l_Lean_Exception_isInterrupt(v_a_1579_);
if (v___x_1590_ == 0)
{
uint8_t v___x_1591_; 
lean_inc(v_a_1579_);
v___x_1591_ = l_Lean_Exception_isRuntime(v_a_1579_);
v___y_1586_ = v___x_1591_;
goto v___jp_1585_;
}
else
{
v___y_1586_ = v___x_1590_;
goto v___jp_1585_;
}
v___jp_1585_:
{
if (v___y_1586_ == 0)
{
if (lean_obj_tag(v_a_1579_) == 0)
{
lean_dec_ref_known(v_a_1579_, 2);
lean_dec_ref_known(v___x_1568_, 3);
lean_dec(v_stx_1552_);
return v___x_1584_;
}
else
{
lean_object* v_id_1587_; uint8_t v___x_1588_; 
v_id_1587_ = lean_ctor_get(v_a_1579_, 0);
lean_inc(v_id_1587_);
lean_dec_ref_known(v_a_1579_, 2);
v___x_1588_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1566_, v_id_1587_);
lean_dec(v_id_1587_);
if (v___x_1588_ == 0)
{
lean_dec_ref_known(v___x_1568_, 3);
lean_dec(v_stx_1552_);
return v___x_1584_;
}
else
{
lean_object* v___x_1589_; 
lean_dec_ref(v___x_1584_);
v___x_1589_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v___x_1568_, v_a_1558_);
lean_dec_ref_known(v___x_1568_, 3);
return v___x_1589_;
}
}
}
else
{
lean_dec(v_a_1579_);
lean_dec_ref_known(v___x_1568_, 3);
lean_dec(v_stx_1552_);
return v___x_1584_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1552_ = stack[0].m_obj;
lean_object* v_a_1553_ = stack[1].m_obj;
lean_object* v_a_1554_ = stack[2].m_obj;
lean_object* v_a_1555_ = stack[3].m_obj;
lean_object* v_a_1556_ = stack[4].m_obj;
lean_object* v_a_1557_ = stack[5].m_obj;
lean_object* v_a_1558_ = stack[6].m_obj;
lean_object* v_res_1594_;
v_res_1594_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_stx_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
stack->m_obj
 = v_res_1594_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_stx_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
return v_res_1603_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(lean_object* v_config_1726_, lean_object* v_item_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_item_1736_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_1740_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1727_, v___x_1739_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1740_) == 0)
{
uint8_t v___x_1741_; 
lean_dec_ref_known(v___x_1740_, 1);
v___x_1741_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1727_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1742_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1727_);
lean_inc_ref(v_item_1727_);
v___x_1743_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1727_);
v___x_1744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_1745_ = lean_string_dec_lt(v___x_1742_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_1747_ = lean_string_dec_lt(v___x_1742_, v___x_1746_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_string_dec_eq(v___x_1742_, v___x_1746_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_1750_ = lean_string_dec_eq(v___x_1742_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_1752_ = lean_string_dec_eq(v___x_1742_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1024257597____hygCtx___hyg_2_));
v___x_1754_ = lean_string_dec_eq(v___x_1742_, v___x_1753_);
lean_dec_ref(v___x_1742_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_1756_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_1755_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1756_) == 0)
{
uint8_t v___x_1757_; 
lean_dec_ref_known(v___x_1756_, 1);
v___x_1757_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_1757_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1758_; 
lean_dec_ref(v___x_1743_);
v___x_1758_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1788_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1788_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1788_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_timeout_1763_; uint8_t v_trimProofs_1764_; uint8_t v_binaryProofs_1765_; uint8_t v_acNf_1766_; uint8_t v_andFlattening_1767_; uint8_t v_embeddedConstraintSubst_1768_; uint8_t v_structures_1769_; uint8_t v_fixedInt_1770_; uint8_t v_enums_1771_; uint8_t v_graphviz_1772_; lean_object* v_maxSteps_1773_; uint8_t v_shortCircuit_1774_; uint8_t v_solverMode_1775_; lean_object* v_cegarRounds_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1787_; 
v_timeout_1763_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_1764_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_1765_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_1766_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_1767_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1768_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_1769_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_1770_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_1771_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_1772_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_1773_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_1774_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_1775_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_cegarRounds_1776_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1778_ = v_config_1726_;
v_isShared_1779_ = v_isSharedCheck_1787_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_cegarRounds_1776_);
lean_inc(v_maxSteps_1773_);
lean_inc(v_timeout_1763_);
lean_dec(v_config_1726_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1787_;
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
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_timeout_1763_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_maxSteps_1773_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_cegarRounds_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3, v_trimProofs_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 1, v_binaryProofs_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 2, v_acNf_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 3, v_andFlattening_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 5, v_structures_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 6, v_fixedInt_1770_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 7, v_enums_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 8, v_graphviz_1772_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 9, v_shortCircuit_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1786_, sizeof(void*)*3 + 10, v_solverMode_1775_);
v___x_1781_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
uint8_t v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_unbox(v_a_1759_);
lean_dec(v_a_1759_);
lean_ctor_set_uint8(v___x_1781_, sizeof(void*)*3 + 11, v___x_1782_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1781_);
v___x_1784_ = v___x_1761_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1781_);
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
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v_config_1726_);
v_a_1789_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1758_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1758_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_1797_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1756_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1756_);
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
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec_ref(v___x_1742_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_1806_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_1805_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1806_) == 0)
{
uint8_t v___x_1807_; 
lean_dec_ref_known(v___x_1806_, 1);
v___x_1807_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v___x_1743_);
v___x_1808_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1838_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_timeout_1813_; uint8_t v_binaryProofs_1814_; uint8_t v_acNf_1815_; uint8_t v_andFlattening_1816_; uint8_t v_embeddedConstraintSubst_1817_; uint8_t v_structures_1818_; uint8_t v_fixedInt_1819_; uint8_t v_enums_1820_; uint8_t v_graphviz_1821_; lean_object* v_maxSteps_1822_; uint8_t v_shortCircuit_1823_; uint8_t v_solverMode_1824_; uint8_t v_uf_1825_; lean_object* v_cegarRounds_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1837_; 
v_timeout_1813_ = lean_ctor_get(v_config_1726_, 0);
v_binaryProofs_1814_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_1815_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_1816_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1817_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_1818_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_1819_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_1820_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_1821_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_1822_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_1823_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_1824_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_1825_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_1826_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1828_ = v_config_1726_;
v_isShared_1829_ = v_isSharedCheck_1837_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_cegarRounds_1826_);
lean_inc(v_maxSteps_1822_);
lean_inc(v_timeout_1813_);
lean_dec(v_config_1726_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1837_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_timeout_1813_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_maxSteps_1822_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_cegarRounds_1826_);
v___x_1831_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
uint8_t v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_unbox(v_a_1809_);
lean_dec(v_a_1809_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3, v___x_1832_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 1, v_binaryProofs_1814_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 2, v_acNf_1815_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 3, v_andFlattening_1816_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1817_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 5, v_structures_1818_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 6, v_fixedInt_1819_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 7, v_enums_1820_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 8, v_graphviz_1821_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 9, v_shortCircuit_1823_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 10, v_solverMode_1824_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3 + 11, v_uf_1825_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1831_);
v___x_1834_ = v___x_1811_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1831_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_config_1726_);
v_a_1839_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1808_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1808_);
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
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_1847_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1806_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1806_);
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
lean_dec_ref(v___x_1742_);
v___x_1855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_1856_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_1855_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1856_) == 0)
{
uint8_t v___x_1857_; 
lean_dec_ref_known(v___x_1856_, 1);
v___x_1857_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_1857_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1858_; 
lean_dec_ref(v___x_1743_);
lean_inc_ref(v_item_1727_);
v___x_1858_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_value_1859_; lean_object* v___x_1860_; 
lean_dec_ref_known(v___x_1858_, 1);
v_value_1859_ = lean_ctor_get(v_item_1727_, 2);
lean_inc(v_value_1859_);
lean_dec_ref(v_item_1727_);
v___x_1860_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1859_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1890_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1890_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1890_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v_trimProofs_1865_; uint8_t v_binaryProofs_1866_; uint8_t v_acNf_1867_; uint8_t v_andFlattening_1868_; uint8_t v_embeddedConstraintSubst_1869_; uint8_t v_structures_1870_; uint8_t v_fixedInt_1871_; uint8_t v_enums_1872_; uint8_t v_graphviz_1873_; lean_object* v_maxSteps_1874_; uint8_t v_shortCircuit_1875_; uint8_t v_solverMode_1876_; uint8_t v_uf_1877_; lean_object* v_cegarRounds_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1888_; 
v_trimProofs_1865_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_1866_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_1867_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_1868_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1869_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_1870_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_1871_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_1872_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_1873_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_1874_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_1875_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_1876_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_1877_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_1878_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v_config_1726_, 0);
lean_dec(v_unused_1889_);
v___x_1880_ = v_config_1726_;
v_isShared_1881_ = v_isSharedCheck_1888_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_cegarRounds_1878_);
lean_inc(v_maxSteps_1874_);
lean_dec(v_config_1726_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1888_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_a_1861_);
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1861_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_maxSteps_1874_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_cegarRounds_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3, v_trimProofs_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 1, v_binaryProofs_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 2, v_acNf_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 3, v_andFlattening_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 5, v_structures_1870_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 6, v_fixedInt_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 7, v_enums_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 8, v_graphviz_1873_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 9, v_shortCircuit_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 10, v_solverMode_1876_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3 + 11, v_uf_1877_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1883_);
v___x_1885_ = v___x_1863_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
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
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v_config_1726_);
v_a_1891_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1860_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1860_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_1899_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1858_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1858_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_1907_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1856_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1856_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec_ref(v___x_1742_);
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_1916_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_1915_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1916_) == 0)
{
uint8_t v___x_1917_; 
lean_dec_ref_known(v___x_1916_, 1);
v___x_1917_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_1917_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1918_; 
lean_dec_ref(v___x_1743_);
v___x_1918_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1948_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1948_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1948_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v_timeout_1923_; uint8_t v_trimProofs_1924_; uint8_t v_binaryProofs_1925_; uint8_t v_acNf_1926_; uint8_t v_andFlattening_1927_; uint8_t v_embeddedConstraintSubst_1928_; uint8_t v_fixedInt_1929_; uint8_t v_enums_1930_; uint8_t v_graphviz_1931_; lean_object* v_maxSteps_1932_; uint8_t v_shortCircuit_1933_; uint8_t v_solverMode_1934_; uint8_t v_uf_1935_; lean_object* v_cegarRounds_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1947_; 
v_timeout_1923_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_1924_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_1925_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_1926_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_1927_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1928_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_fixedInt_1929_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_1930_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_1931_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_1932_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_1933_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_1934_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_1935_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_1936_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1938_ = v_config_1726_;
v_isShared_1939_ = v_isSharedCheck_1947_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_cegarRounds_1936_);
lean_inc(v_maxSteps_1932_);
lean_inc(v_timeout_1923_);
lean_dec(v_config_1726_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1947_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_timeout_1923_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_maxSteps_1932_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_cegarRounds_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*3, v_trimProofs_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*3 + 1, v_binaryProofs_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*3 + 2, v_acNf_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*3 + 3, v_andFlattening_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1928_);
v___x_1941_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
uint8_t v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_unbox(v_a_1919_);
lean_dec(v_a_1919_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*3 + 5, v___x_1942_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*3 + 6, v_fixedInt_1929_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*3 + 7, v_enums_1930_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*3 + 8, v_graphviz_1931_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*3 + 9, v_shortCircuit_1933_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*3 + 10, v_solverMode_1934_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*3 + 11, v_uf_1935_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1941_);
v___x_1944_ = v___x_1921_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1941_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_config_1726_);
v_a_1949_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1918_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1918_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_1957_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1916_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1916_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
else
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_string_dec_eq(v___x_1742_, v___x_1744_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_1967_ = lean_string_dec_eq(v___x_1742_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10));
v___x_1969_ = lean_string_dec_eq(v___x_1742_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11));
v___x_1971_ = lean_string_dec_eq(v___x_1742_, v___x_1970_);
lean_dec_ref(v___x_1742_);
if (v___x_1971_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12));
v___x_1973_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_1972_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1973_) == 0)
{
uint8_t v___x_1974_; 
lean_dec_ref_known(v___x_1973_, 1);
v___x_1974_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_1974_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1975_; 
lean_dec_ref(v___x_1743_);
lean_inc_ref(v_item_1727_);
v___x_1975_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_value_1976_; lean_object* v___x_1977_; 
lean_dec_ref_known(v___x_1975_, 1);
v_value_1976_ = lean_ctor_get(v_item_1727_, 2);
lean_inc(v_value_1976_);
lean_dec_ref(v_item_1727_);
v___x_1977_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_value_1976_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2007_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2007_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2007_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_timeout_1982_; uint8_t v_trimProofs_1983_; uint8_t v_binaryProofs_1984_; uint8_t v_acNf_1985_; uint8_t v_andFlattening_1986_; uint8_t v_embeddedConstraintSubst_1987_; uint8_t v_structures_1988_; uint8_t v_fixedInt_1989_; uint8_t v_enums_1990_; uint8_t v_graphviz_1991_; lean_object* v_maxSteps_1992_; uint8_t v_shortCircuit_1993_; uint8_t v_uf_1994_; lean_object* v_cegarRounds_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2006_; 
v_timeout_1982_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_1983_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_1984_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_1985_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_1986_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1987_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_1988_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_1989_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_1990_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_1991_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_1992_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_1993_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_uf_1994_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_1995_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1997_ = v_config_1726_;
v_isShared_1998_ = v_isSharedCheck_2006_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_cegarRounds_1995_);
lean_inc(v_maxSteps_1992_);
lean_inc(v_timeout_1982_);
lean_dec(v_config_1726_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2006_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_timeout_1982_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_maxSteps_1992_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_cegarRounds_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3, v_trimProofs_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 1, v_binaryProofs_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 2, v_acNf_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 3, v_andFlattening_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 5, v_structures_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 6, v_fixedInt_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 7, v_enums_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 8, v_graphviz_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*3 + 9, v_shortCircuit_1993_);
v___x_2000_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
uint8_t v___x_2001_; lean_object* v___x_2003_; 
v___x_2001_ = lean_unbox(v_a_1978_);
lean_dec(v_a_1978_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*3 + 10, v___x_2001_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*3 + 11, v_uf_1994_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_2000_);
v___x_2003_ = v___x_1980_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2000_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_config_1726_);
v_a_2008_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1977_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1977_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2016_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1975_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1975_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2024_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1973_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1973_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v___x_1742_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13));
v___x_2033_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2032_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2033_) == 0)
{
uint8_t v___x_2034_; 
lean_dec_ref_known(v___x_2033_, 1);
v___x_2034_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2035_; 
lean_dec_ref(v___x_1743_);
v___x_2035_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2065_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2065_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2065_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_timeout_2040_; uint8_t v_trimProofs_2041_; uint8_t v_binaryProofs_2042_; uint8_t v_acNf_2043_; uint8_t v_andFlattening_2044_; uint8_t v_embeddedConstraintSubst_2045_; uint8_t v_structures_2046_; uint8_t v_fixedInt_2047_; uint8_t v_enums_2048_; uint8_t v_graphviz_2049_; lean_object* v_maxSteps_2050_; uint8_t v_solverMode_2051_; uint8_t v_uf_2052_; lean_object* v_cegarRounds_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2064_; 
v_timeout_2040_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2041_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2042_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2043_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2044_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2045_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2046_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2047_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2048_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2049_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2050_ = lean_ctor_get(v_config_1726_, 1);
v_solverMode_2051_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2052_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2053_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2055_ = v_config_1726_;
v_isShared_2056_ = v_isSharedCheck_2064_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_cegarRounds_2053_);
lean_inc(v_maxSteps_2050_);
lean_inc(v_timeout_2040_);
lean_dec(v_config_1726_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2064_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_timeout_2040_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_maxSteps_2050_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_cegarRounds_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3, v_trimProofs_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 1, v_binaryProofs_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 2, v_acNf_2043_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 3, v_andFlattening_2044_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 5, v_structures_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 6, v_fixedInt_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 7, v_enums_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2063_, sizeof(void*)*3 + 8, v_graphviz_2049_);
v___x_2058_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
uint8_t v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_unbox(v_a_2036_);
lean_dec(v_a_2036_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*3 + 9, v___x_2059_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*3 + 10, v_solverMode_2051_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*3 + 11, v_uf_2052_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2058_);
v___x_2061_ = v___x_2038_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2058_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_config_1726_);
v_a_2066_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2035_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2035_);
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
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2074_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2033_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2033_);
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
lean_dec_ref(v___x_1742_);
v___x_2082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14));
v___x_2083_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2082_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2083_) == 0)
{
uint8_t v___x_2084_; 
lean_dec_ref_known(v___x_2083_, 1);
v___x_2084_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2085_; 
lean_dec_ref(v___x_1743_);
lean_inc_ref(v_item_1727_);
v___x_2085_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_value_2086_; lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2085_, 1);
v_value_2086_ = lean_ctor_get(v_item_1727_, 2);
lean_inc(v_value_2086_);
lean_dec_ref(v_item_1727_);
v___x_2087_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_2086_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2117_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2117_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2117_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_timeout_2092_; uint8_t v_trimProofs_2093_; uint8_t v_binaryProofs_2094_; uint8_t v_acNf_2095_; uint8_t v_andFlattening_2096_; uint8_t v_embeddedConstraintSubst_2097_; uint8_t v_structures_2098_; uint8_t v_fixedInt_2099_; uint8_t v_enums_2100_; uint8_t v_graphviz_2101_; uint8_t v_shortCircuit_2102_; uint8_t v_solverMode_2103_; uint8_t v_uf_2104_; lean_object* v_cegarRounds_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2115_; 
v_timeout_2092_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2093_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2094_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2095_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2096_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2097_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2098_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2099_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2100_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2101_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_shortCircuit_2102_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2103_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2104_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2105_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v_config_1726_, 1);
lean_dec(v_unused_2116_);
v___x_2107_ = v_config_1726_;
v_isShared_2108_ = v_isSharedCheck_2115_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_cegarRounds_2105_);
lean_inc(v_timeout_2092_);
lean_dec(v_config_1726_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2115_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 1, v_a_2088_);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_timeout_2092_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_a_2088_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_cegarRounds_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3, v_trimProofs_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 1, v_binaryProofs_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 2, v_acNf_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 3, v_andFlattening_2096_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 5, v_structures_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 6, v_fixedInt_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 7, v_enums_2100_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 8, v_graphviz_2101_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 9, v_shortCircuit_2102_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 10, v_solverMode_2103_);
lean_ctor_set_uint8(v_reuseFailAlloc_2114_, sizeof(void*)*3 + 11, v_uf_2104_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2110_);
v___x_2112_ = v___x_2090_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v_config_1726_);
v_a_2118_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2087_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2087_);
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
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2126_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2085_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2085_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2134_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2083_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2083_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v___x_1742_);
v___x_2142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15));
v___x_2143_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2142_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2143_) == 0)
{
uint8_t v___x_2144_; 
lean_dec_ref_known(v___x_2143_, 1);
v___x_2144_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2144_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2145_; 
lean_dec_ref(v___x_1743_);
v___x_2145_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2175_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2175_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2175_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_timeout_2150_; uint8_t v_trimProofs_2151_; uint8_t v_binaryProofs_2152_; uint8_t v_acNf_2153_; uint8_t v_andFlattening_2154_; uint8_t v_embeddedConstraintSubst_2155_; uint8_t v_structures_2156_; uint8_t v_fixedInt_2157_; uint8_t v_enums_2158_; lean_object* v_maxSteps_2159_; uint8_t v_shortCircuit_2160_; uint8_t v_solverMode_2161_; uint8_t v_uf_2162_; lean_object* v_cegarRounds_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2174_; 
v_timeout_2150_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2151_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2152_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2153_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2154_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2155_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2156_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2157_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2158_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_maxSteps_2159_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2160_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2161_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2162_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2163_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2165_ = v_config_1726_;
v_isShared_2166_ = v_isSharedCheck_2174_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_cegarRounds_2163_);
lean_inc(v_maxSteps_2159_);
lean_inc(v_timeout_2150_);
lean_dec(v_config_1726_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2174_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_timeout_2150_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_maxSteps_2159_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_cegarRounds_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3, v_trimProofs_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3 + 1, v_binaryProofs_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3 + 2, v_acNf_2153_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3 + 3, v_andFlattening_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3 + 5, v_structures_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3 + 6, v_fixedInt_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2173_, sizeof(void*)*3 + 7, v_enums_2158_);
v___x_2168_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
uint8_t v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_unbox(v_a_2146_);
lean_dec(v_a_2146_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*3 + 8, v___x_2169_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*3 + 9, v_shortCircuit_2160_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*3 + 10, v_solverMode_2161_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*3 + 11, v_uf_2162_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2168_);
v___x_2171_ = v___x_2148_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2168_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_config_1726_);
v_a_2176_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2145_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2145_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2184_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2143_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2143_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
else
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16));
v___x_2193_ = lean_string_dec_lt(v___x_1742_, v___x_2192_);
if (v___x_2193_ == 0)
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_string_dec_eq(v___x_1742_, v___x_2192_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17));
v___x_2196_ = lean_string_dec_eq(v___x_1742_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18));
v___x_2198_ = lean_string_dec_eq(v___x_1742_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19));
v___x_2200_ = lean_string_dec_eq(v___x_1742_, v___x_2199_);
lean_dec_ref(v___x_1742_);
if (v___x_2200_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20));
v___x_2202_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2201_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2202_) == 0)
{
uint8_t v___x_2203_; 
lean_dec_ref_known(v___x_2202_, 1);
v___x_2203_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2203_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2204_; 
lean_dec_ref(v___x_1743_);
v___x_2204_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2234_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2234_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2234_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_timeout_2209_; uint8_t v_trimProofs_2210_; uint8_t v_binaryProofs_2211_; uint8_t v_acNf_2212_; uint8_t v_andFlattening_2213_; uint8_t v_embeddedConstraintSubst_2214_; uint8_t v_structures_2215_; uint8_t v_enums_2216_; uint8_t v_graphviz_2217_; lean_object* v_maxSteps_2218_; uint8_t v_shortCircuit_2219_; uint8_t v_solverMode_2220_; uint8_t v_uf_2221_; lean_object* v_cegarRounds_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2233_; 
v_timeout_2209_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2210_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2211_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2212_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2213_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2214_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2215_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_enums_2216_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2217_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2218_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2219_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2220_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2221_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2222_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2224_ = v_config_1726_;
v_isShared_2225_ = v_isSharedCheck_2233_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_cegarRounds_2222_);
lean_inc(v_maxSteps_2218_);
lean_inc(v_timeout_2209_);
lean_dec(v_config_1726_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2233_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_timeout_2209_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_maxSteps_2218_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_cegarRounds_2222_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3, v_trimProofs_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3 + 1, v_binaryProofs_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3 + 2, v_acNf_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3 + 3, v_andFlattening_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*3 + 5, v_structures_2215_);
v___x_2227_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
uint8_t v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = lean_unbox(v_a_2205_);
lean_dec(v_a_2205_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*3 + 6, v___x_2228_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*3 + 7, v_enums_2216_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*3 + 8, v_graphviz_2217_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*3 + 9, v_shortCircuit_2219_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*3 + 10, v_solverMode_2220_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*3 + 11, v_uf_2221_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2227_);
v___x_2230_ = v___x_2207_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2227_);
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
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v_config_1726_);
v_a_2235_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2204_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2204_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2243_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2202_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2202_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v___x_1742_);
v___x_2251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21));
v___x_2252_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2251_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2252_) == 0)
{
uint8_t v___x_2253_; 
lean_dec_ref_known(v___x_2252_, 1);
v___x_2253_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2253_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2254_; 
lean_dec_ref(v___x_1743_);
v___x_2254_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2284_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2284_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2284_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v_timeout_2259_; uint8_t v_trimProofs_2260_; uint8_t v_binaryProofs_2261_; uint8_t v_acNf_2262_; uint8_t v_andFlattening_2263_; uint8_t v_embeddedConstraintSubst_2264_; uint8_t v_structures_2265_; uint8_t v_fixedInt_2266_; uint8_t v_graphviz_2267_; lean_object* v_maxSteps_2268_; uint8_t v_shortCircuit_2269_; uint8_t v_solverMode_2270_; uint8_t v_uf_2271_; lean_object* v_cegarRounds_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2283_; 
v_timeout_2259_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2260_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2261_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2262_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2263_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2264_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2265_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2266_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_graphviz_2267_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2268_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2269_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2270_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2271_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2272_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2274_ = v_config_1726_;
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_cegarRounds_2272_);
lean_inc(v_maxSteps_2268_);
lean_inc(v_timeout_2259_);
lean_dec(v_config_1726_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_timeout_2259_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_maxSteps_2268_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_cegarRounds_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*3, v_trimProofs_2260_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*3 + 1, v_binaryProofs_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*3 + 2, v_acNf_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*3 + 3, v_andFlattening_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*3 + 5, v_structures_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2282_, sizeof(void*)*3 + 6, v_fixedInt_2266_);
v___x_2277_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
uint8_t v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3 + 7, v___x_2278_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3 + 8, v_graphviz_2267_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3 + 9, v_shortCircuit_2269_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3 + 10, v_solverMode_2270_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3 + 11, v_uf_2271_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2277_);
v___x_2280_ = v___x_2257_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2277_);
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
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v_config_1726_);
v_a_2285_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2254_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2254_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2293_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2252_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2252_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v___x_1742_);
v___x_2301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22));
v___x_2302_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2301_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2302_) == 0)
{
uint8_t v___x_2303_; 
lean_dec_ref_known(v___x_2302_, 1);
v___x_2303_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2303_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2304_; 
lean_dec_ref(v___x_1743_);
v___x_2304_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2334_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2334_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2334_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_timeout_2309_; uint8_t v_trimProofs_2310_; uint8_t v_binaryProofs_2311_; uint8_t v_acNf_2312_; uint8_t v_andFlattening_2313_; uint8_t v_structures_2314_; uint8_t v_fixedInt_2315_; uint8_t v_enums_2316_; uint8_t v_graphviz_2317_; lean_object* v_maxSteps_2318_; uint8_t v_shortCircuit_2319_; uint8_t v_solverMode_2320_; uint8_t v_uf_2321_; lean_object* v_cegarRounds_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2333_; 
v_timeout_2309_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2310_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2311_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2312_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2313_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_structures_2314_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2315_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2316_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2317_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2318_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2319_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2320_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2321_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2322_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2324_ = v_config_1726_;
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_cegarRounds_2322_);
lean_inc(v_maxSteps_2318_);
lean_inc(v_timeout_2309_);
lean_dec(v_config_1726_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2333_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_timeout_2309_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_maxSteps_2318_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_cegarRounds_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3, v_trimProofs_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3 + 1, v_binaryProofs_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3 + 2, v_acNf_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3 + 3, v_andFlattening_2313_);
v___x_2327_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
uint8_t v___x_2328_; lean_object* v___x_2330_; 
v___x_2328_ = lean_unbox(v_a_2305_);
lean_dec(v_a_2305_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 4, v___x_2328_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 5, v_structures_2314_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 6, v_fixedInt_2315_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 7, v_enums_2316_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 8, v_graphviz_2317_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 9, v_shortCircuit_2319_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 10, v_solverMode_2320_);
lean_ctor_set_uint8(v___x_2327_, sizeof(void*)*3 + 11, v_uf_2321_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2327_);
v___x_2330_ = v___x_2307_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2327_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_config_1726_);
v_a_2335_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2304_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2304_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2343_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2302_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2302_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
uint8_t v___x_2351_; 
lean_dec_ref(v___x_1742_);
lean_dec_ref(v_config_1726_);
v___x_2351_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2351_ == 0)
{
lean_dec_ref(v_item_1727_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v_value_2352_; lean_object* v___x_2353_; 
lean_dec_ref(v___x_1743_);
v_value_2352_ = lean_ctor_get(v_item_1727_, 2);
lean_inc(v_value_2352_);
lean_dec_ref(v_item_1727_);
v___x_2353_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_value_2352_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_2353_;
}
}
}
else
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23));
v___x_2355_ = lean_string_dec_eq(v___x_1742_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24));
v___x_2357_ = lean_string_dec_eq(v___x_1742_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25));
v___x_2359_ = lean_string_dec_eq(v___x_1742_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26));
v___x_2361_ = lean_string_dec_eq(v___x_1742_, v___x_2360_);
lean_dec_ref(v___x_1742_);
if (v___x_2361_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27));
v___x_2363_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2362_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2363_) == 0)
{
uint8_t v___x_2364_; 
lean_dec_ref_known(v___x_2363_, 1);
v___x_2364_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2364_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2365_; 
lean_dec_ref(v___x_1743_);
lean_inc_ref(v_item_1727_);
v___x_2365_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_value_2366_; lean_object* v___x_2367_; 
lean_dec_ref_known(v___x_2365_, 1);
v_value_2366_ = lean_ctor_get(v_item_1727_, 2);
lean_inc(v_value_2366_);
lean_dec_ref(v_item_1727_);
v___x_2367_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_2366_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2397_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2397_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2397_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_timeout_2372_; uint8_t v_trimProofs_2373_; uint8_t v_binaryProofs_2374_; uint8_t v_acNf_2375_; uint8_t v_andFlattening_2376_; uint8_t v_embeddedConstraintSubst_2377_; uint8_t v_structures_2378_; uint8_t v_fixedInt_2379_; uint8_t v_enums_2380_; uint8_t v_graphviz_2381_; lean_object* v_maxSteps_2382_; uint8_t v_shortCircuit_2383_; uint8_t v_solverMode_2384_; uint8_t v_uf_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2395_; 
v_timeout_2372_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2373_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2374_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2375_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2376_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2377_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2378_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2379_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2380_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2381_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2382_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2383_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2384_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2385_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v_config_1726_, 2);
lean_dec(v_unused_2396_);
v___x_2387_ = v_config_1726_;
v_isShared_2388_ = v_isSharedCheck_2395_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_maxSteps_2382_);
lean_inc(v_timeout_2372_);
lean_dec(v_config_1726_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2395_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 2, v_a_2368_);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_timeout_2372_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_maxSteps_2382_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_a_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3, v_trimProofs_2373_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 1, v_binaryProofs_2374_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 2, v_acNf_2375_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 3, v_andFlattening_2376_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2377_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 5, v_structures_2378_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 6, v_fixedInt_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 7, v_enums_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 8, v_graphviz_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 9, v_shortCircuit_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 10, v_solverMode_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2394_, sizeof(void*)*3 + 11, v_uf_2385_);
v___x_2390_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2392_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2390_);
v___x_2392_ = v___x_2370_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v_config_1726_);
v_a_2398_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2367_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2367_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2406_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2365_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2365_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2414_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2363_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2363_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref(v___x_1742_);
v___x_2422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__28));
v___x_2423_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2422_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2423_) == 0)
{
uint8_t v___x_2424_; 
lean_dec_ref_known(v___x_2423_, 1);
v___x_2424_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2424_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2425_; 
lean_dec_ref(v___x_1743_);
v___x_2425_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2455_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2455_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2455_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_timeout_2430_; uint8_t v_trimProofs_2431_; uint8_t v_acNf_2432_; uint8_t v_andFlattening_2433_; uint8_t v_embeddedConstraintSubst_2434_; uint8_t v_structures_2435_; uint8_t v_fixedInt_2436_; uint8_t v_enums_2437_; uint8_t v_graphviz_2438_; lean_object* v_maxSteps_2439_; uint8_t v_shortCircuit_2440_; uint8_t v_solverMode_2441_; uint8_t v_uf_2442_; lean_object* v_cegarRounds_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2454_; 
v_timeout_2430_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2431_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_acNf_2432_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_andFlattening_2433_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2434_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2435_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2436_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2437_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2438_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2439_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2440_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2441_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2442_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2443_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2445_ = v_config_1726_;
v_isShared_2446_ = v_isSharedCheck_2454_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_cegarRounds_2443_);
lean_inc(v_maxSteps_2439_);
lean_inc(v_timeout_2430_);
lean_dec(v_config_1726_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2454_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_timeout_2430_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_maxSteps_2439_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_cegarRounds_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2453_, sizeof(void*)*3, v_trimProofs_2431_);
v___x_2448_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
uint8_t v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = lean_unbox(v_a_2426_);
lean_dec(v_a_2426_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 1, v___x_2449_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 2, v_acNf_2432_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 3, v_andFlattening_2433_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2434_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 5, v_structures_2435_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 6, v_fixedInt_2436_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 7, v_enums_2437_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 8, v_graphviz_2438_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 9, v_shortCircuit_2440_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 10, v_solverMode_2441_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*3 + 11, v_uf_2442_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2448_);
v___x_2451_ = v___x_2428_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2448_);
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
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_config_1726_);
v_a_2456_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2425_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2425_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2464_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2423_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2423_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec_ref(v___x_1742_);
v___x_2472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__29));
v___x_2473_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2472_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2473_) == 0)
{
uint8_t v___x_2474_; 
lean_dec_ref_known(v___x_2473_, 1);
v___x_2474_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2474_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2475_; 
lean_dec_ref(v___x_1743_);
v___x_2475_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2505_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2505_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2505_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v_timeout_2480_; uint8_t v_trimProofs_2481_; uint8_t v_binaryProofs_2482_; uint8_t v_acNf_2483_; uint8_t v_embeddedConstraintSubst_2484_; uint8_t v_structures_2485_; uint8_t v_fixedInt_2486_; uint8_t v_enums_2487_; uint8_t v_graphviz_2488_; lean_object* v_maxSteps_2489_; uint8_t v_shortCircuit_2490_; uint8_t v_solverMode_2491_; uint8_t v_uf_2492_; lean_object* v_cegarRounds_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2504_; 
v_timeout_2480_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2481_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2482_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_acNf_2483_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 2);
v_embeddedConstraintSubst_2484_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2485_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2486_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2487_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2488_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2489_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2490_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2491_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2492_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2493_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2495_ = v_config_1726_;
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_cegarRounds_2493_);
lean_inc(v_maxSteps_2489_);
lean_inc(v_timeout_2480_);
lean_dec(v_config_1726_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_timeout_2480_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_maxSteps_2489_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_cegarRounds_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2503_, sizeof(void*)*3, v_trimProofs_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2503_, sizeof(void*)*3 + 1, v_binaryProofs_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2503_, sizeof(void*)*3 + 2, v_acNf_2483_);
v___x_2498_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
uint8_t v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = lean_unbox(v_a_2476_);
lean_dec(v_a_2476_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 3, v___x_2499_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2484_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 5, v_structures_2485_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 6, v_fixedInt_2486_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 7, v_enums_2487_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 8, v_graphviz_2488_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 9, v_shortCircuit_2490_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 10, v_solverMode_2491_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 11, v_uf_2492_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2498_);
v___x_2501_ = v___x_2478_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2498_);
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
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v_config_1726_);
v_a_2506_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2475_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2475_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2514_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2473_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2473_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec_ref(v___x_1742_);
v___x_2522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__30));
v___x_2523_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1727_, v___x_2522_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2523_) == 0)
{
uint8_t v___x_2524_; 
lean_dec_ref_known(v___x_2523_, 1);
v___x_2524_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1743_);
if (v___x_2524_ == 0)
{
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_item_1736_ = v___x_1743_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_2525_; 
lean_dec_ref(v___x_1743_);
v___x_2525_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2555_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2555_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2555_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_timeout_2530_; uint8_t v_trimProofs_2531_; uint8_t v_binaryProofs_2532_; uint8_t v_andFlattening_2533_; uint8_t v_embeddedConstraintSubst_2534_; uint8_t v_structures_2535_; uint8_t v_fixedInt_2536_; uint8_t v_enums_2537_; uint8_t v_graphviz_2538_; lean_object* v_maxSteps_2539_; uint8_t v_shortCircuit_2540_; uint8_t v_solverMode_2541_; uint8_t v_uf_2542_; lean_object* v_cegarRounds_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2554_; 
v_timeout_2530_ = lean_ctor_get(v_config_1726_, 0);
v_trimProofs_2531_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3);
v_binaryProofs_2532_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 1);
v_andFlattening_2533_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_2534_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 4);
v_structures_2535_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 5);
v_fixedInt_2536_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 6);
v_enums_2537_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 7);
v_graphviz_2538_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 8);
v_maxSteps_2539_ = lean_ctor_get(v_config_1726_, 1);
v_shortCircuit_2540_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 9);
v_solverMode_2541_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 10);
v_uf_2542_ = lean_ctor_get_uint8(v_config_1726_, sizeof(void*)*3 + 11);
v_cegarRounds_2543_ = lean_ctor_get(v_config_1726_, 2);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_config_1726_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2545_ = v_config_1726_;
v_isShared_2546_ = v_isSharedCheck_2554_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_cegarRounds_2543_);
lean_inc(v_maxSteps_2539_);
lean_inc(v_timeout_2530_);
lean_dec(v_config_1726_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2554_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_timeout_2530_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_maxSteps_2539_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_cegarRounds_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2553_, sizeof(void*)*3, v_trimProofs_2531_);
lean_ctor_set_uint8(v_reuseFailAlloc_2553_, sizeof(void*)*3 + 1, v_binaryProofs_2532_);
v___x_2548_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
uint8_t v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 2, v___x_2549_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 3, v_andFlattening_2533_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_2534_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 5, v_structures_2535_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 6, v_fixedInt_2536_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 7, v_enums_2537_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 8, v_graphviz_2538_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 9, v_shortCircuit_2540_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 10, v_solverMode_2541_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3 + 11, v_uf_2542_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2548_);
v___x_2551_ = v___x_2528_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2548_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_config_1726_);
v_a_2556_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2525_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2525_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2564_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2523_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2523_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_config_1726_);
v_item_1736_ = v_item_1727_;
goto v___jp_1735_;
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v_item_1727_);
lean_dec_ref(v_config_1726_);
v_a_2572_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_1740_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_1740_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
v___jp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_1738_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1736_, v___x_1737_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1738_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1726_ = stack[0].m_obj;
lean_object* v_item_1727_ = stack[1].m_obj;
lean_object* v___y_1728_ = stack[2].m_obj;
lean_object* v___y_1729_ = stack[3].m_obj;
lean_object* v___y_1730_ = stack[4].m_obj;
lean_object* v___y_1731_ = stack[5].m_obj;
lean_object* v___y_1732_ = stack[6].m_obj;
lean_object* v___y_1733_ = stack[7].m_obj;
lean_object* v_res_2580_;
v_res_2580_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(v_config_1726_, v_item_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
stack->m_obj
 = v_res_2580_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_2581_, lean_object* v_item_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(v_config_2581_, v_item_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2590_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object* v_e_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_2593_, v___y_2597_);
return v___x_2601_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2593_ = stack[0].m_obj;
lean_object* v___y_2594_ = stack[1].m_obj;
lean_object* v___y_2595_ = stack[2].m_obj;
lean_object* v___y_2596_ = stack[3].m_obj;
lean_object* v___y_2597_ = stack[4].m_obj;
lean_object* v___y_2598_ = stack[5].m_obj;
lean_object* v___y_2599_ = stack[6].m_obj;
lean_object* v_res_2602_;
v_res_2602_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(v_e_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
stack->m_obj
 = v_res_2602_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_e_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(v_e_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2611_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object* v_00_u03b1_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v___x_2620_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2613_ = stack[1].m_obj;
lean_object* v___y_2614_ = stack[2].m_obj;
lean_object* v___y_2615_ = stack[3].m_obj;
lean_object* v___y_2616_ = stack[4].m_obj;
lean_object* v___y_2617_ = stack[5].m_obj;
lean_object* v___y_2618_ = stack[6].m_obj;
lean_object* v_res_2621_;
v_res_2621_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_box(0), v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
stack->m_obj
 = v_res_2621_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(v_00_u03b1_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2630_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object* v_00_u03b1_2631_, lean_object* v_msg_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2632_ = stack[1].m_obj;
lean_object* v___y_2633_ = stack[2].m_obj;
lean_object* v___y_2634_ = stack[3].m_obj;
lean_object* v___y_2635_ = stack[4].m_obj;
lean_object* v___y_2636_ = stack[5].m_obj;
lean_object* v___y_2637_ = stack[6].m_obj;
lean_object* v___y_2638_ = stack[7].m_obj;
lean_object* v_res_2641_;
v_res_2641_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_box(0), v_msg_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
stack->m_obj
 = v_res_2641_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_msg_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(v_00_u03b1_2642_, v_msg_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
return v_res_2651_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object* v_msgData_2652_, lean_object* v_macroStack_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_2652_, v_macroStack_2653_, v___y_2658_);
return v___x_2661_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2652_ = stack[0].m_obj;
lean_object* v_macroStack_2653_ = stack[1].m_obj;
lean_object* v___y_2654_ = stack[2].m_obj;
lean_object* v___y_2655_ = stack[3].m_obj;
lean_object* v___y_2656_ = stack[4].m_obj;
lean_object* v___y_2657_ = stack[5].m_obj;
lean_object* v___y_2658_ = stack[6].m_obj;
lean_object* v___y_2659_ = stack[7].m_obj;
lean_object* v_res_2662_;
v_res_2662_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(v_msgData_2652_, v_macroStack_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
stack->m_obj
 = v_res_2662_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object* v_msgData_2663_, lean_object* v_macroStack_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(v_msgData_2663_, v_macroStack_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2672_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = lean_box(0);
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_2675_ = l_Lean_mkConst(v___x_2674_, v___x_2673_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
return v___x_2677_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(lean_object* v_cfg_2678_, lean_object* v_cfgItem_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1);
v___x_2688_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2678_, v_cfgItem_2679_, v___x_2687_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
return v___x_2688_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2678_ = stack[0].m_obj;
lean_object* v_cfgItem_2679_ = stack[1].m_obj;
lean_object* v___y_2680_ = stack[2].m_obj;
lean_object* v___y_2681_ = stack[3].m_obj;
lean_object* v___y_2682_ = stack[4].m_obj;
lean_object* v___y_2683_ = stack[5].m_obj;
lean_object* v___y_2684_ = stack[6].m_obj;
lean_object* v___y_2685_ = stack[7].m_obj;
lean_object* v_res_2689_;
v_res_2689_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(v_cfg_2678_, v_cfgItem_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
stack->m_obj
 = v_res_2689_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_2690_, lean_object* v_cfgItem_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(v_cfg_2690_, v_cfgItem_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v_cfgItem_2691_);
return v_res_2699_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object* v_cfg_2701_, lean_object* v_init_2702_, uint8_t v_logExceptions_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_onErr_2708_; lean_object* v_eval_2709_; 
v_onErr_2708_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0));
v_eval_2709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_2703_ == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2709_, v_init_2702_, v_cfg_2701_, v_onErr_2708_, v_logExceptions_2703_, v_a_2705_, v_a_2706_);
return v___x_2710_;
}
else
{
uint8_t v_recover_2711_; lean_object* v___x_2712_; 
v_recover_2711_ = lean_ctor_get_uint8(v_a_2704_, sizeof(void*)*1);
v___x_2712_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2709_, v_init_2702_, v_cfg_2701_, v_onErr_2708_, v_recover_2711_, v_a_2705_, v_a_2706_);
return v___x_2712_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2701_ = stack[0].m_obj;
lean_object* v_init_2702_ = stack[1].m_obj;
uint8_t v_logExceptions_2703_ = stack[2].m_num;
lean_object* v_a_2704_ = stack[3].m_obj;
lean_object* v_a_2705_ = stack[4].m_obj;
lean_object* v_a_2706_ = stack[5].m_obj;
lean_object* v_res_2713_;
v_res_2713_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2701_, v_init_2702_, v_logExceptions_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
stack->m_obj
 = v_res_2713_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_2714_, lean_object* v_init_2715_, lean_object* v_logExceptions_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
uint8_t v_logExceptions_boxed_2721_; lean_object* v_res_2722_; 
v_logExceptions_boxed_2721_ = lean_unbox(v_logExceptions_2716_);
v_res_2722_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2714_, v_init_2715_, v_logExceptions_boxed_2721_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2722_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(lean_object* v_cfg_2723_, lean_object* v_init_2724_, uint8_t v_logExceptions_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2723_, v_init_2724_, v_logExceptions_2725_, v_a_2726_, v_a_2732_, v_a_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2723_ = stack[0].m_obj;
lean_object* v_init_2724_ = stack[1].m_obj;
uint8_t v_logExceptions_2725_ = stack[2].m_num;
lean_object* v_a_2726_ = stack[3].m_obj;
lean_object* v_a_2727_ = stack[4].m_obj;
lean_object* v_a_2728_ = stack[5].m_obj;
lean_object* v_a_2729_ = stack[6].m_obj;
lean_object* v_a_2730_ = stack[7].m_obj;
lean_object* v_a_2731_ = stack[8].m_obj;
lean_object* v_a_2732_ = stack[9].m_obj;
lean_object* v_a_2733_ = stack[10].m_obj;
lean_object* v_res_2736_;
v_res_2736_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(v_cfg_2723_, v_init_2724_, v_logExceptions_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___boxed(lean_object* v_cfg_2737_, lean_object* v_init_2738_, lean_object* v_logExceptions_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
uint8_t v_logExceptions_boxed_2749_; lean_object* v_res_2750_; 
v_logExceptions_boxed_2749_ = lean_unbox(v_logExceptions_2739_);
v_res_2750_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(v_cfg_2737_, v_init_2738_, v_logExceptions_boxed_2749_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
return v_res_2750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2751_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2754_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2756_ = lean_unsigned_to_nat(0u);
v___x_2757_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_ctor_set(v___x_2757_, 2, v___x_2756_);
lean_ctor_set(v___x_2757_, 3, v___x_2756_);
lean_ctor_set(v___x_2757_, 4, v___x_2755_);
lean_ctor_set(v___x_2757_, 5, v___x_2755_);
lean_ctor_set(v___x_2757_, 6, v___x_2755_);
lean_ctor_set(v___x_2757_, 7, v___x_2755_);
lean_ctor_set(v___x_2757_, 8, v___x_2755_);
lean_ctor_set(v___x_2757_, 9, v___x_2755_);
lean_ctor_set(v___x_2757_, 10, v___x_2755_);
lean_ctor_set(v___x_2757_, 11, v___x_2754_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2758_ = lean_unsigned_to_nat(32u);
v___x_2759_ = lean_mk_empty_array_with_capacity(v___x_2758_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2761_ = ((size_t)5ULL);
v___x_2762_ = lean_unsigned_to_nat(0u);
v___x_2763_ = lean_unsigned_to_nat(32u);
v___x_2764_ = lean_mk_empty_array_with_capacity(v___x_2763_);
v___x_2765_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3);
v___x_2766_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2764_);
lean_ctor_set(v___x_2766_, 2, v___x_2762_);
lean_ctor_set(v___x_2766_, 3, v___x_2762_);
lean_ctor_set_usize(v___x_2766_, 4, v___x_2761_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2767_ = lean_box(1);
v___x_2768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4);
v___x_2769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___x_2768_);
lean_ctor_set(v___x_2770_, 2, v___x_2767_);
return v___x_2770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__6));
v___x_2773_ = l_Lean_stringToMessageData(v___x_2772_);
return v___x_2773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__8));
v___x_2776_ = l_Lean_stringToMessageData(v___x_2775_);
return v___x_2776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__10));
v___x_2779_ = l_Lean_stringToMessageData(v___x_2778_);
return v___x_2779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__12));
v___x_2782_ = l_Lean_stringToMessageData(v___x_2781_);
return v___x_2782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__14));
v___x_2785_ = l_Lean_stringToMessageData(v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16));
v___x_2788_ = l_Lean_stringToMessageData(v___x_2787_);
return v___x_2788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18));
v___x_2791_ = l_Lean_stringToMessageData(v___x_2790_);
return v___x_2791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__20));
v___x_2794_ = l_Lean_stringToMessageData(v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__23(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__22));
v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__25(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__24));
v___x_2800_ = l_Lean_stringToMessageData(v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__27(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__26));
v___x_2803_ = l_Lean_stringToMessageData(v___x_2802_);
return v___x_2803_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_msg_2804_, lean_object* v_declHint_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v_env_2810_; uint8_t v___x_2811_; 
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_st_ref_get(v___y_2806_);
v_env_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc_ref(v_env_2810_);
lean_dec(v___x_2809_);
v___x_2811_ = l_Lean_Name_isAnonymous(v_declHint_2805_);
if (v___x_2811_ == 0)
{
uint8_t v_isExporting_2812_; 
v_isExporting_2812_ = lean_ctor_get_uint8(v_env_2810_, sizeof(void*)*13);
if (v_isExporting_2812_ == 0)
{
lean_object* v___x_2813_; 
lean_dec_ref(v_env_2810_);
lean_dec(v_declHint_2805_);
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v_msg_2804_);
return v___x_2813_;
}
else
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
lean_inc_ref(v_env_2810_);
v___x_2814_ = l_Lean_Environment_setExporting(v_env_2810_, v___x_2811_);
lean_inc(v_declHint_2805_);
lean_inc_ref(v___x_2814_);
v___x_2815_ = l_Lean_Environment_contains(v___x_2814_, v_declHint_2805_, v_isExporting_2812_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
lean_dec_ref(v___x_2814_);
lean_dec_ref(v_env_2810_);
lean_dec(v_declHint_2805_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_msg_2804_);
return v___x_2816_;
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v_c_2822_; lean_object* v___x_2823_; 
v___x_2817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
v___x_2819_ = l_Lean_Options_empty;
v___x_2820_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2814_);
lean_ctor_set(v___x_2820_, 1, v___x_2817_);
lean_ctor_set(v___x_2820_, 2, v___x_2818_);
lean_ctor_set(v___x_2820_, 3, v___x_2819_);
lean_inc(v_declHint_2805_);
v___x_2821_ = l_Lean_MessageData_ofConstName(v_declHint_2805_, v___x_2811_);
v_c_2822_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2822_, 0, v___x_2820_);
lean_ctor_set(v_c_2822_, 1, v___x_2821_);
v___x_2823_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2810_, v_declHint_2805_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec_ref(v_env_2810_);
lean_dec(v_declHint_2805_);
v___x_2824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
lean_ctor_set(v___x_2825_, 1, v_c_2822_);
v___x_2826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_MessageData_note(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_msg_2804_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
else
{
lean_object* v_val_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2887_; 
v_val_2831_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2833_ = v___x_2823_;
v_isShared_2834_ = v_isSharedCheck_2887_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_val_2831_);
lean_dec(v___x_2823_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2887_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v_modules_2836_; lean_object* v_moduleNames_2837_; lean_object* v_mod_2838_; uint8_t v___y_2840_; uint8_t v___x_2870_; 
v___x_2835_ = l_Lean_Environment_header(v_env_2810_);
lean_dec_ref(v_env_2810_);
v_modules_2836_ = lean_ctor_get(v___x_2835_, 3);
lean_inc_ref(v_modules_2836_);
v_moduleNames_2837_ = lean_ctor_get(v___x_2835_, 4);
lean_inc_ref(v_moduleNames_2837_);
lean_dec_ref(v___x_2835_);
v_mod_2838_ = lean_array_get(v___x_2808_, v_moduleNames_2837_, v_val_2831_);
lean_dec_ref(v_moduleNames_2837_);
v___x_2870_ = l_Lean_isPrivateName(v_declHint_2805_);
lean_dec(v_declHint_2805_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = lean_array_get_size(v_modules_2836_);
v___x_2872_ = lean_nat_dec_lt(v_val_2831_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_dec_ref(v_modules_2836_);
lean_dec(v_val_2831_);
v___y_2840_ = v___x_2870_;
goto v___jp_2839_;
}
else
{
lean_object* v___x_2873_; lean_object* v_toImport_2874_; uint8_t v_isExported_2875_; 
v___x_2873_ = lean_array_fget(v_modules_2836_, v_val_2831_);
lean_dec(v_val_2831_);
lean_dec_ref(v_modules_2836_);
v_toImport_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc_ref(v_toImport_2874_);
lean_dec(v___x_2873_);
v_isExported_2875_ = lean_ctor_get_uint8(v_toImport_2874_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2874_);
v___y_2840_ = v_isExported_2875_;
goto v___jp_2839_;
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec_ref(v_modules_2836_);
lean_del_object(v___x_2833_);
lean_dec(v_val_2831_);
v___x_2876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v_c_2822_);
v___x_2878_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__25);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Lean_MessageData_ofName(v_mod_2838_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__27);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = l_Lean_MessageData_note(v___x_2883_);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v_msg_2804_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
v___jp_2839_:
{
if (v___y_2840_ == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v_c_2822_);
v___x_2843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = l_Lean_MessageData_ofName(v_mod_2838_);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_MessageData_note(v___x_2848_);
v___x_2850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_msg_2804_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2850_);
v___x_2852_ = v___x_2833_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v_c_2822_);
v___x_2856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Lean_MessageData_ofName(v_mod_2838_);
lean_inc_ref(v___x_2858_);
v___x_2859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2857_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__21);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2859_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v___x_2858_);
v___x_2863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__23);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_MessageData_note(v___x_2864_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v_msg_2804_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2866_);
v___x_2868_ = v___x_2833_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2888_; 
lean_dec_ref(v_env_2810_);
lean_dec(v_declHint_2805_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_msg_2804_);
return v___x_2888_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2804_ = stack[0].m_obj;
lean_object* v_declHint_2805_ = stack[1].m_obj;
lean_object* v___y_2806_ = stack[2].m_obj;
lean_object* v_res_2889_;
v_res_2889_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2804_, v_declHint_2805_, v___y_2806_);
stack->m_obj
 = v_res_2889_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2890_, lean_object* v_declHint_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2890_, v_declHint_2891_, v___y_2892_);
lean_dec(v___y_2892_);
return v_res_2894_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_msg_2895_, lean_object* v_declHint_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2910_; 
v___x_2900_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2895_, v_declHint_2896_, v___y_2898_);
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2910_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2910_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2905_ = l_Lean_unknownIdentifierMessageTag;
v___x_2906_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v_a_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2906_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2895_ = stack[0].m_obj;
lean_object* v_declHint_2896_ = stack[1].m_obj;
lean_object* v___y_2897_ = stack[2].m_obj;
lean_object* v___y_2898_ = stack[3].m_obj;
lean_object* v_res_2911_;
v_res_2911_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2895_, v_declHint_2896_, v___y_2897_, v___y_2898_);
stack->m_obj
 = v_res_2911_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_msg_2912_, lean_object* v_declHint_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2912_, v_declHint_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2917_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(lean_object* v_msgData_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; lean_object* v_toCold_2923_; lean_object* v_env_2924_; lean_object* v_options_2925_; uint8_t v___x_2926_; lean_object* v_env_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2922_ = lean_st_ref_get(v___y_2920_);
v_toCold_2923_ = lean_ctor_get(v___y_2919_, 0);
v_env_2924_ = lean_ctor_get(v___x_2922_, 0);
lean_inc_ref(v_env_2924_);
lean_dec(v___x_2922_);
v_options_2925_ = lean_ctor_get(v_toCold_2923_, 2);
v___x_2926_ = 0;
v_env_2927_ = l_Lean_Environment_setRecordingDeps(v_env_2924_, v___x_2926_);
v___x_2928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2929_ = lean_unsigned_to_nat(32u);
v___x_2930_ = lean_mk_empty_array_with_capacity(v___x_2929_);
lean_dec_ref(v___x_2930_);
v___x_2931_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2925_);
v___x_2932_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2932_, 0, v_env_2927_);
lean_ctor_set(v___x_2932_, 1, v___x_2928_);
lean_ctor_set(v___x_2932_, 2, v___x_2931_);
lean_ctor_set(v___x_2932_, 3, v_options_2925_);
v___x_2933_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v_msgData_2918_);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2918_ = stack[0].m_obj;
lean_object* v___y_2919_ = stack[1].m_obj;
lean_object* v___y_2920_ = stack[2].m_obj;
lean_object* v_res_2935_;
v_res_2935_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msgData_2918_, v___y_2919_, v___y_2920_);
stack->m_obj
 = v_res_2935_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msgData_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
return v_res_2940_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_msg_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_ref_2945_; lean_object* v___x_2946_; lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2955_; 
v_ref_2945_ = lean_ctor_get(v___y_2942_, 2);
v___x_2946_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msg_2941_, v___y_2942_, v___y_2943_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
lean_inc(v_ref_2945_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v_ref_2945_);
lean_ctor_set(v___x_2951_, 1, v_a_2947_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 1);
lean_ctor_set(v___x_2949_, 0, v___x_2951_);
v___x_2953_ = v___x_2949_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2941_ = stack[0].m_obj;
lean_object* v___y_2942_ = stack[1].m_obj;
lean_object* v___y_2943_ = stack[2].m_obj;
lean_object* v_res_2956_;
v_res_2956_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2941_, v___y_2942_, v___y_2943_);
stack->m_obj
 = v_res_2956_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_msg_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
return v_res_2961_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_ref_2962_, lean_object* v_msg_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_toCold_2967_; lean_object* v_currRecDepth_2968_; lean_object* v_ref_2969_; uint16_t v_optionFlags_2970_; uint8_t v_suppressElabErrors_2971_; uint8_t v_isRecordingDeps_2972_; lean_object* v_ref_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_toCold_2967_ = lean_ctor_get(v___y_2964_, 0);
v_currRecDepth_2968_ = lean_ctor_get(v___y_2964_, 1);
v_ref_2969_ = lean_ctor_get(v___y_2964_, 2);
v_optionFlags_2970_ = lean_ctor_get_uint16(v___y_2964_, sizeof(void*)*3);
v_suppressElabErrors_2971_ = lean_ctor_get_uint8(v___y_2964_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2972_ = lean_ctor_get_uint8(v___y_2964_, sizeof(void*)*3 + 3);
v_ref_2973_ = l_Lean_replaceRef(v_ref_2962_, v_ref_2969_);
lean_inc(v_currRecDepth_2968_);
lean_inc_ref(v_toCold_2967_);
v___x_2974_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2974_, 0, v_toCold_2967_);
lean_ctor_set(v___x_2974_, 1, v_currRecDepth_2968_);
lean_ctor_set(v___x_2974_, 2, v_ref_2973_);
lean_ctor_set_uint16(v___x_2974_, sizeof(void*)*3, v_optionFlags_2970_);
lean_ctor_set_uint8(v___x_2974_, sizeof(void*)*3 + 2, v_suppressElabErrors_2971_);
lean_ctor_set_uint8(v___x_2974_, sizeof(void*)*3 + 3, v_isRecordingDeps_2972_);
v___x_2975_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2963_, v___x_2974_, v___y_2965_);
lean_dec_ref_known(v___x_2974_, 3);
return v___x_2975_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2962_ = stack[0].m_obj;
lean_object* v_msg_2963_ = stack[1].m_obj;
lean_object* v___y_2964_ = stack[2].m_obj;
lean_object* v___y_2965_ = stack[3].m_obj;
lean_object* v_res_2976_;
v_res_2976_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2962_, v_msg_2963_, v___y_2964_, v___y_2965_);
stack->m_obj
 = v_res_2976_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_ref_2977_, lean_object* v_msg_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2977_, v_msg_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v_ref_2977_);
return v_res_2982_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2983_, lean_object* v_msg_2984_, lean_object* v_declHint_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; lean_object* v_a_2990_; lean_object* v___x_2991_; 
v___x_2989_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2984_, v_declHint_2985_, v___y_2986_, v___y_2987_);
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2983_, v_a_2990_, v___y_2986_, v___y_2987_);
return v___x_2991_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2983_ = stack[0].m_obj;
lean_object* v_msg_2984_ = stack[1].m_obj;
lean_object* v_declHint_2985_ = stack[2].m_obj;
lean_object* v___y_2986_ = stack[3].m_obj;
lean_object* v___y_2987_ = stack[4].m_obj;
lean_object* v_res_2992_;
v_res_2992_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2983_, v_msg_2984_, v_declHint_2985_, v___y_2986_, v___y_2987_);
stack->m_obj
 = v_res_2992_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2993_, lean_object* v_msg_2994_, lean_object* v_declHint_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2993_, v_msg_2994_, v_declHint_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v_ref_2993_);
return v_res_2999_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_3002_ = l_Lean_stringToMessageData(v___x_3001_);
return v___x_3002_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3003_, lean_object* v_constName_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3008_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3009_ = 0;
lean_inc(v_constName_3004_);
v___x_3010_ = l_Lean_MessageData_ofConstName(v_constName_3004_, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3008_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3003_, v___x_3013_, v_constName_3004_, v___y_3005_, v___y_3006_);
return v___x_3014_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3003_ = stack[0].m_obj;
lean_object* v_constName_3004_ = stack[1].m_obj;
lean_object* v___y_3005_ = stack[2].m_obj;
lean_object* v___y_3006_ = stack[3].m_obj;
lean_object* v_res_3015_;
v_res_3015_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_3003_, v_constName_3004_, v___y_3005_, v___y_3006_);
stack->m_obj
 = v_res_3015_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3016_, lean_object* v_constName_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_3016_, v_constName_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v_ref_3016_);
return v_res_3021_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(lean_object* v_constName_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_ref_3026_; lean_object* v___x_3027_; 
v_ref_3026_ = lean_ctor_get(v___y_3023_, 2);
v___x_3027_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_3026_, v_constName_3022_, v___y_3023_, v___y_3024_);
return v___x_3027_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3022_ = stack[0].m_obj;
lean_object* v___y_3023_ = stack[1].m_obj;
lean_object* v___y_3024_ = stack[2].m_obj;
lean_object* v_res_3028_;
v_res_3028_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_3022_, v___y_3023_, v___y_3024_);
stack->m_obj
 = v_res_3028_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
return v_res_3033_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(lean_object* v_constName_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v_env_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3038_ = lean_st_ref_get(v___y_3036_);
v_env_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc_ref(v_env_3039_);
lean_dec(v___x_3038_);
v___x_3040_ = 0;
lean_inc(v_constName_3034_);
v___x_3041_ = l_Lean_Environment_find_x3f(v_env_3039_, v_constName_3034_, v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_3034_, v___y_3035_, v___y_3036_);
return v___x_3042_;
}
else
{
lean_object* v_val_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_constName_3034_);
v_val_3043_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3041_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_val_3043_);
lean_dec(v___x_3041_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 0);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_val_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3034_ = stack[0].m_obj;
lean_object* v___y_3035_ = stack[1].m_obj;
lean_object* v___y_3036_ = stack[2].m_obj;
lean_object* v_res_3051_;
v_res_3051_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_constName_3034_, v___y_3035_, v___y_3036_);
stack->m_obj
 = v_res_3051_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0___boxed(lean_object* v_constName_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_constName_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v_res_3056_;
}
}
lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(uint8_t v___x_3057_, lean_object* v_x_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
if (lean_obj_tag(v_x_3058_) == 0)
{
uint8_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = 1;
v___x_3063_ = lean_box(v___x_3062_);
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
else
{
lean_object* v_head_3065_; lean_object* v_tail_3066_; lean_object* v___y_3068_; uint8_t v_a_3069_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_head_3065_ = lean_ctor_get(v_x_3058_, 0);
lean_inc(v_head_3065_);
v_tail_3066_ = lean_ctor_get(v_x_3058_, 1);
lean_inc(v_tail_3066_);
lean_dec_ref_known(v_x_3058_, 2);
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_head_3065_, v___y_3059_, v___y_3060_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3088_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3088_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3088_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
if (lean_obj_tag(v_a_3073_) == 6)
{
lean_object* v_val_3077_; lean_object* v_numFields_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v_val_3077_ = lean_ctor_get(v_a_3073_, 0);
lean_inc_ref(v_val_3077_);
lean_dec_ref_known(v_a_3073_, 1);
v_numFields_3078_ = lean_ctor_get(v_val_3077_, 4);
lean_inc(v_numFields_3078_);
lean_dec_ref(v_val_3077_);
v___x_3079_ = lean_nat_dec_eq(v_numFields_3078_, v___x_3071_);
lean_dec(v_numFields_3078_);
v___x_3080_ = lean_box(v___x_3079_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3080_);
v___x_3082_ = v___x_3075_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
v___y_3068_ = v___x_3082_;
v_a_3069_ = v___x_3079_;
goto v___jp_3067_;
}
}
else
{
lean_object* v___x_3084_; lean_object* v___x_3086_; 
lean_dec(v_a_3073_);
v___x_3084_ = lean_box(v___x_3057_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3084_);
v___x_3086_ = v___x_3075_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
v___y_3068_ = v___x_3086_;
v_a_3069_ = v___x_3057_;
goto v___jp_3067_;
}
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_tail_3066_);
v_a_3089_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3072_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3072_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
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
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
v___jp_3067_:
{
if (v_a_3069_ == 0)
{
lean_dec(v_tail_3066_);
return v___y_3068_;
}
else
{
lean_dec_ref(v___y_3068_);
v_x_3058_ = v_tail_3066_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3057_ = stack[0].m_num;
lean_object* v_x_3058_ = stack[1].m_obj;
lean_object* v___y_3059_ = stack[2].m_obj;
lean_object* v___y_3060_ = stack[3].m_obj;
lean_object* v_res_3097_;
v_res_3097_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v___x_3057_, v_x_3058_, v___y_3059_, v___y_3060_);
stack->m_obj
 = v_res_3097_;
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2___boxed(lean_object* v___x_3098_, lean_object* v_x_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
uint8_t v___x_4674__boxed_3103_; lean_object* v_res_3104_; 
v___x_4674__boxed_3103_ = lean_unbox(v___x_3098_);
v_res_3104_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v___x_4674__boxed_3103_, v_x_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
return v_res_3104_;
}
}
lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(lean_object* v_declName_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3165_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3165_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3165_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
if (lean_obj_tag(v_a_3110_) == 5)
{
lean_object* v_val_3114_; lean_object* v_toConstantVal_3115_; lean_object* v_numParams_3116_; lean_object* v_numIndices_3117_; lean_object* v_ctors_3118_; uint8_t v_isRec_3119_; uint8_t v_isUnsafe_3120_; lean_object* v_type_3121_; uint8_t v___x_3122_; 
v_val_3114_ = lean_ctor_get(v_a_3110_, 0);
lean_inc_ref(v_val_3114_);
lean_dec_ref_known(v_a_3110_, 1);
v_toConstantVal_3115_ = lean_ctor_get(v_val_3114_, 0);
v_numParams_3116_ = lean_ctor_get(v_val_3114_, 1);
lean_inc(v_numParams_3116_);
v_numIndices_3117_ = lean_ctor_get(v_val_3114_, 2);
lean_inc(v_numIndices_3117_);
v_ctors_3118_ = lean_ctor_get(v_val_3114_, 4);
lean_inc(v_ctors_3118_);
v_isRec_3119_ = lean_ctor_get_uint8(v_val_3114_, sizeof(void*)*6);
v_isUnsafe_3120_ = lean_ctor_get_uint8(v_val_3114_, sizeof(void*)*6 + 1);
v_type_3121_ = lean_ctor_get(v_toConstantVal_3115_, 2);
v___x_3122_ = l_Lean_Expr_isProp(v_type_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3123_ = l_Lean_InductiveVal_numTypeFormers(v_val_3114_);
lean_dec_ref(v_val_3114_);
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_dec_eq(v___x_3123_, v___x_3124_);
lean_dec(v___x_3123_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
lean_dec(v_ctors_3118_);
lean_dec(v_numIndices_3117_);
lean_dec(v_numParams_3116_);
v___x_3126_ = lean_box(v___x_3125_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3126_);
v___x_3128_ = v___x_3112_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
else
{
lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3130_ = lean_unsigned_to_nat(0u);
v___x_3131_ = lean_nat_dec_eq(v_numIndices_3117_, v___x_3130_);
lean_dec(v_numIndices_3117_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
lean_dec(v_ctors_3118_);
lean_dec(v_numParams_3116_);
v___x_3132_ = lean_box(v___x_3131_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3132_);
v___x_3134_ = v___x_3112_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
else
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_nat_dec_eq(v_numParams_3116_, v___x_3130_);
lean_dec(v_numParams_3116_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_dec(v_ctors_3118_);
v___x_3137_ = lean_box(v___x_3136_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3137_);
v___x_3139_ = v___x_3112_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
else
{
uint8_t v___x_3141_; 
v___x_3141_ = l_List_isEmpty___redArg(v_ctors_3118_);
if (v___x_3141_ == 0)
{
if (v_isRec_3119_ == 0)
{
if (v_isUnsafe_3120_ == 0)
{
lean_object* v___x_3142_; 
lean_del_object(v___x_3112_);
v___x_3142_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v_isUnsafe_3120_, v_ctors_3118_, v___y_3106_, v___y_3107_);
return v___x_3142_;
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
lean_dec(v_ctors_3118_);
v___x_3143_ = lean_box(v_isRec_3119_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3143_);
v___x_3145_ = v___x_3112_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
lean_dec(v_ctors_3118_);
v___x_3147_ = lean_box(v___x_3141_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3147_);
v___x_3149_ = v___x_3112_;
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
else
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_dec(v_ctors_3118_);
v___x_3151_ = lean_box(v___x_3122_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3151_);
v___x_3153_ = v___x_3112_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
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
}
else
{
uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
lean_dec(v_ctors_3118_);
lean_dec(v_numIndices_3117_);
lean_dec(v_numParams_3116_);
lean_dec_ref(v_val_3114_);
v___x_3155_ = 0;
v___x_3156_ = lean_box(v___x_3155_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3156_);
v___x_3158_ = v___x_3112_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
else
{
uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; 
lean_dec(v_a_3110_);
v___x_3160_ = 0;
v___x_3161_ = lean_box(v___x_3160_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3161_);
v___x_3163_ = v___x_3112_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
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
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
v_a_3166_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3109_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3109_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3105_ = stack[0].m_obj;
lean_object* v___y_3106_ = stack[1].m_obj;
lean_object* v___y_3107_ = stack[2].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_3105_, v___y_3106_, v___y_3107_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1___boxed(lean_object* v_declName_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3179_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object* v_cfg_3180_, lean_object* v_declName_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_){
_start:
{
uint8_t v_structures_3185_; uint8_t v_enums_3186_; uint8_t v_a_3188_; 
v_structures_3185_ = lean_ctor_get_uint8(v_cfg_3180_, sizeof(void*)*3 + 5);
v_enums_3186_ = lean_ctor_get_uint8(v_cfg_3180_, sizeof(void*)*3 + 7);
if (v_enums_3186_ == 0)
{
v_a_3188_ = v_enums_3186_;
goto v___jp_3187_;
}
else
{
lean_object* v___x_3226_; 
lean_inc(v_declName_3181_);
v___x_3226_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_3181_, v_a_3182_, v_a_3183_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3237_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3237_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3237_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
uint8_t v___x_3231_; 
v___x_3231_ = lean_unbox(v_a_3227_);
if (v___x_3231_ == 0)
{
uint8_t v___x_3232_; 
lean_del_object(v___x_3229_);
v___x_3232_ = lean_unbox(v_a_3227_);
lean_dec(v_a_3227_);
v_a_3188_ = v___x_3232_;
goto v___jp_3187_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
lean_dec(v_a_3227_);
lean_dec(v_declName_3181_);
v___x_3233_ = lean_box(v_enums_3186_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3233_);
v___x_3235_ = v___x_3229_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_dec(v_declName_3181_);
return v___x_3226_;
}
}
v___jp_3187_:
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_st_ref_get(v_a_3183_);
if (v_structures_3185_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec(v___x_3189_);
lean_dec(v_declName_3181_);
v___x_3190_ = lean_box(v_a_3188_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
else
{
if (v_a_3188_ == 0)
{
lean_object* v_env_3192_; uint8_t v___x_3193_; 
v_env_3192_ = lean_ctor_get(v___x_3189_, 0);
lean_inc_ref(v_env_3192_);
lean_dec(v___x_3189_);
lean_inc(v_declName_3181_);
v___x_3193_ = l_Lean_isStructure(v_env_3192_, v_declName_3181_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec(v_declName_3181_);
v___x_3194_ = lean_box(v_a_3188_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_3181_, v_a_3182_, v_a_3183_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3215_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3215_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3215_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
if (lean_obj_tag(v_a_3197_) == 5)
{
lean_object* v_val_3201_; uint8_t v_isRec_3202_; 
v_val_3201_ = lean_ctor_get(v_a_3197_, 0);
lean_inc_ref(v_val_3201_);
lean_dec_ref_known(v_a_3197_, 1);
v_isRec_3202_ = lean_ctor_get_uint8(v_val_3201_, sizeof(void*)*6);
lean_dec_ref(v_val_3201_);
if (v_isRec_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_box(v___x_3193_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3203_);
v___x_3205_ = v___x_3199_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3207_ = lean_box(v_a_3188_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3207_);
v___x_3209_ = v___x_3199_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
lean_dec(v_a_3197_);
v___x_3211_ = lean_box(v_a_3188_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3211_);
v___x_3213_ = v___x_3199_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
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
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
v_a_3216_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3196_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3196_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec(v___x_3189_);
lean_dec(v_declName_3181_);
v___x_3224_ = lean_box(v_a_3188_);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
return v___x_3225_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3180_ = stack[0].m_obj;
lean_object* v_declName_3181_ = stack[1].m_obj;
lean_object* v_a_3182_ = stack[2].m_obj;
lean_object* v_a_3183_ = stack[3].m_obj;
lean_object* v_res_3238_;
v_res_3238_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3180_, v_declName_3181_, v_a_3182_, v_a_3183_);
stack->m_obj
 = v_res_3238_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType___boxed(lean_object* v_cfg_3239_, lean_object* v_declName_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3239_, v_declName_3240_, v_a_3241_, v_a_3242_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec_ref(v_cfg_3239_);
return v_res_3244_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(lean_object* v_00_u03b1_3245_, lean_object* v_constName_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_3246_, v___y_3247_, v___y_3248_);
return v___x_3250_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3246_ = stack[1].m_obj;
lean_object* v___y_3247_ = stack[2].m_obj;
lean_object* v___y_3248_ = stack[3].m_obj;
lean_object* v_res_3251_;
v_res_3251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(lean_box(0), v_constName_3246_, v___y_3247_, v___y_3248_);
stack->m_obj
 = v_res_3251_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3252_, lean_object* v_constName_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(v_00_u03b1_3252_, v_constName_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3257_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3258_, lean_object* v_ref_3259_, lean_object* v_constName_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_3259_, v_constName_3260_, v___y_3261_, v___y_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3259_ = stack[1].m_obj;
lean_object* v_constName_3260_ = stack[2].m_obj;
lean_object* v___y_3261_ = stack[3].m_obj;
lean_object* v___y_3262_ = stack[4].m_obj;
lean_object* v_res_3265_;
v_res_3265_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(lean_box(0), v_ref_3259_, v_constName_3260_, v___y_3261_, v___y_3262_);
stack->m_obj
 = v_res_3265_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3266_, lean_object* v_ref_3267_, lean_object* v_constName_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(v_00_u03b1_3266_, v_ref_3267_, v_constName_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v_ref_3267_);
return v_res_3272_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_3273_, lean_object* v_ref_3274_, lean_object* v_msg_3275_, lean_object* v_declHint_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3274_, v_msg_3275_, v_declHint_3276_, v___y_3277_, v___y_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3274_ = stack[1].m_obj;
lean_object* v_msg_3275_ = stack[2].m_obj;
lean_object* v_declHint_3276_ = stack[3].m_obj;
lean_object* v___y_3277_ = stack[4].m_obj;
lean_object* v___y_3278_ = stack[5].m_obj;
lean_object* v_res_3281_;
v_res_3281_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_ref_3274_, v_msg_3275_, v_declHint_3276_, v___y_3277_, v___y_3278_);
stack->m_obj
 = v_res_3281_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3282_, lean_object* v_ref_3283_, lean_object* v_msg_3284_, lean_object* v_declHint_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3282_, v_ref_3283_, v_msg_3284_, v_declHint_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v_ref_3283_);
return v_res_3289_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_3290_, lean_object* v_declHint_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_3290_, v_declHint_3291_, v___y_3293_);
return v___x_3295_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3290_ = stack[0].m_obj;
lean_object* v_declHint_3291_ = stack[1].m_obj;
lean_object* v___y_3292_ = stack[2].m_obj;
lean_object* v___y_3293_ = stack[3].m_obj;
lean_object* v_res_3296_;
v_res_3296_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3290_, v_declHint_3291_, v___y_3292_, v___y_3293_);
stack->m_obj
 = v_res_3296_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3297_, lean_object* v_declHint_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3297_, v_declHint_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
return v_res_3302_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b1_3303_, lean_object* v_ref_3304_, lean_object* v_msg_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_3304_, v_msg_3305_, v___y_3306_, v___y_3307_);
return v___x_3309_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3304_ = stack[1].m_obj;
lean_object* v_msg_3305_ = stack[2].m_obj;
lean_object* v___y_3306_ = stack[3].m_obj;
lean_object* v___y_3307_ = stack[4].m_obj;
lean_object* v_res_3310_;
v_res_3310_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(lean_box(0), v_ref_3304_, v_msg_3305_, v___y_3306_, v___y_3307_);
stack->m_obj
 = v_res_3310_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b1_3311_, lean_object* v_ref_3312_, lean_object* v_msg_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03b1_3311_, v_ref_3312_, v_msg_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v_ref_3312_);
return v_res_3317_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b1_3318_, lean_object* v_msg_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_3319_, v___y_3320_, v___y_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3319_ = stack[1].m_obj;
lean_object* v___y_3320_ = stack[2].m_obj;
lean_object* v___y_3321_ = stack[3].m_obj;
lean_object* v_res_3324_;
v_res_3324_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(lean_box(0), v_msg_3319_, v___y_3320_, v___y_3321_);
stack->m_obj
 = v_res_3324_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3325_, lean_object* v_msg_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(v_00_u03b1_3325_, v_msg_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3330_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(lean_object* v_a_3331_, lean_object* v_as_3332_, size_t v_i_3333_, size_t v_stop_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_eq(v_i_3333_, v_stop_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = lean_array_uget_borrowed(v_as_3332_, v_i_3333_);
v___x_3337_ = lean_name_eq(v_a_3331_, v___x_3336_);
if (v___x_3337_ == 0)
{
size_t v___x_3338_; size_t v___x_3339_; 
v___x_3338_ = ((size_t)1ULL);
v___x_3339_ = lean_usize_add(v_i_3333_, v___x_3338_);
v_i_3333_ = v___x_3339_;
goto _start;
}
else
{
return v___x_3337_;
}
}
else
{
uint8_t v___x_3341_; 
v___x_3341_ = 0;
return v___x_3341_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3331_ = stack[0].m_obj;
lean_object* v_as_3332_ = stack[1].m_obj;
size_t v_i_3333_ = stack[2].m_num;
size_t v_stop_3334_ = stack[3].m_num;
uint8_t v_res_3342_;
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3331_, v_as_3332_, v_i_3333_, v_stop_3334_);
stack->m_num = v_res_3342_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0___boxed(lean_object* v_a_3343_, lean_object* v_as_3344_, lean_object* v_i_3345_, lean_object* v_stop_3346_){
_start:
{
size_t v_i_boxed_3347_; size_t v_stop_boxed_3348_; uint8_t v_res_3349_; lean_object* v_r_3350_; 
v_i_boxed_3347_ = lean_unbox_usize(v_i_3345_);
lean_dec(v_i_3345_);
v_stop_boxed_3348_ = lean_unbox_usize(v_stop_3346_);
lean_dec(v_stop_3346_);
v_res_3349_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3343_, v_as_3344_, v_i_boxed_3347_, v_stop_boxed_3348_);
lean_dec_ref(v_as_3344_);
lean_dec(v_a_3343_);
v_r_3350_ = lean_box(v_res_3349_);
return v_r_3350_;
}
}
uint8_t l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(lean_object* v_as_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_array_get_size(v_as_3351_);
v___x_3355_ = lean_nat_dec_lt(v___x_3353_, v___x_3354_);
if (v___x_3355_ == 0)
{
return v___x_3355_;
}
else
{
if (v___x_3355_ == 0)
{
return v___x_3355_;
}
else
{
size_t v___x_3356_; size_t v___x_3357_; uint8_t v___x_3358_; 
v___x_3356_ = ((size_t)0ULL);
v___x_3357_ = lean_usize_of_nat(v___x_3354_);
v___x_3358_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3352_, v_as_3351_, v___x_3356_, v___x_3357_);
return v___x_3358_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3351_ = stack[0].m_obj;
lean_object* v_a_3352_ = stack[1].m_obj;
uint8_t v_res_3359_;
v_res_3359_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_as_3351_, v_a_3352_);
stack->m_num = v_res_3359_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0___boxed(lean_object* v_as_3360_, lean_object* v_a_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_as_3360_, v_a_3361_);
lean_dec(v_a_3361_);
lean_dec_ref(v_as_3360_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__0));
v___x_3366_ = l_Lean_stringToMessageData(v___x_3365_);
return v___x_3366_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(lean_object* v_cfg_3367_, lean_object* v_as_3368_, size_t v_sz_3369_, size_t v_i_3370_, lean_object* v_b_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_a_3376_; uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_lt(v_i_3370_, v_sz_3369_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_b_3371_);
return v___x_3381_;
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_a_3382_ = lean_array_uget_borrowed(v_as_3368_, v_i_3370_);
v___x_3383_ = lean_box(0);
lean_inc(v_a_3382_);
v___x_3384_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_3382_, v___x_3383_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3389_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc_n(v_a_3385_, 2);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3389_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3367_, v_a_3385_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; uint8_t v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v___x_3391_ = lean_unbox(v_a_3390_);
lean_dec(v_a_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3392_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
lean_inc(v_a_3385_);
v___x_3393_ = l_Lean_MessageData_ofName(v_a_3385_);
v___x_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___x_3395_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1);
v___x_3396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_a_3382_, v___x_3396_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_dec_ref_known(v___x_3397_, 1);
goto v___jp_3386_;
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_a_3385_);
lean_dec_ref(v_b_3371_);
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
goto v___jp_3386_;
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_a_3385_);
lean_dec_ref(v_b_3371_);
v_a_3406_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3389_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3389_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
v___jp_3386_:
{
uint8_t v___x_3387_; 
v___x_3387_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_b_3371_, v_a_3385_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_array_push(v_b_3371_, v_a_3385_);
v_a_3376_ = v___x_3388_;
goto v___jp_3375_;
}
else
{
lean_dec(v_a_3385_);
v_a_3376_ = v_b_3371_;
goto v___jp_3375_;
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec_ref(v_b_3371_);
v_a_3414_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3384_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3384_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
v___jp_3375_:
{
size_t v___x_3377_; size_t v___x_3378_; 
v___x_3377_ = ((size_t)1ULL);
v___x_3378_ = lean_usize_add(v_i_3370_, v___x_3377_);
v_i_3370_ = v___x_3378_;
v_b_3371_ = v_a_3376_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3367_ = stack[0].m_obj;
lean_object* v_as_3368_ = stack[1].m_obj;
size_t v_sz_3369_ = stack[2].m_num;
size_t v_i_3370_ = stack[3].m_num;
lean_object* v_b_3371_ = stack[4].m_obj;
lean_object* v___y_3372_ = stack[5].m_obj;
lean_object* v___y_3373_ = stack[6].m_obj;
lean_object* v_res_3422_;
v_res_3422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3367_, v_as_3368_, v_sz_3369_, v_i_3370_, v_b_3371_, v___y_3372_, v___y_3373_);
stack->m_obj
 = v_res_3422_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___boxed(lean_object* v_cfg_3423_, lean_object* v_as_3424_, lean_object* v_sz_3425_, lean_object* v_i_3426_, lean_object* v_b_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
size_t v_sz_boxed_3431_; size_t v_i_boxed_3432_; lean_object* v_res_3433_; 
v_sz_boxed_3431_ = lean_unbox_usize(v_sz_3425_);
lean_dec(v_sz_3425_);
v_i_boxed_3432_ = lean_unbox_usize(v_i_3426_);
lean_dec(v_i_3426_);
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3423_, v_as_3424_, v_sz_boxed_3431_, v_i_boxed_3432_, v_b_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v_as_3424_);
lean_dec_ref(v_cfg_3423_);
return v_res_3433_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__3));
v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
return v___x_3443_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object* v_stx_3446_, lean_object* v_cfg_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
if (lean_obj_tag(v_stx_3446_) == 1)
{
lean_object* v_val_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3486_; 
v_val_3451_ = lean_ctor_get(v_stx_3446_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_stx_3446_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3453_ = v_stx_3446_;
v_isShared_3454_ = v_isSharedCheck_3486_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_val_3451_);
lean_dec(v_stx_3446_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3486_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3455_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2));
lean_inc(v_val_3451_);
v___x_3456_ = l_Lean_Syntax_isOfKind(v_val_3451_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_del_object(v___x_3453_);
v___x_3457_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4);
v___x_3458_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_val_3451_, v___x_3457_, v_a_3448_, v_a_3449_);
lean_dec(v_val_3451_);
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v_ids_3461_; lean_object* v_types_3462_; lean_object* v___x_3463_; size_t v_sz_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3459_ = lean_unsigned_to_nat(2u);
v___x_3460_ = l_Lean_Syntax_getArg(v_val_3451_, v___x_3459_);
lean_dec(v_val_3451_);
v_ids_3461_ = l_Lean_Syntax_getArgs(v___x_3460_);
lean_dec(v___x_3460_);
v_types_3462_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__5));
v___x_3463_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ids_3461_);
lean_dec_ref(v_ids_3461_);
v_sz_3464_ = lean_array_size(v___x_3463_);
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3447_, v___x_3463_, v_sz_3464_, v___x_3465_, v_types_3462_, v_a_3448_, v_a_3449_);
lean_dec_ref(v___x_3463_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3477_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3477_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3477_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v_a_3467_);
v___x_3472_ = v___x_3453_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3474_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3472_);
v___x_3474_ = v___x_3469_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_del_object(v___x_3453_);
v_a_3478_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3466_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3466_);
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
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec(v_stx_3446_);
v___x_3487_ = lean_box(0);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3446_ = stack[0].m_obj;
lean_object* v_cfg_3447_ = stack[1].m_obj;
lean_object* v_a_3448_ = stack[2].m_obj;
lean_object* v_a_3449_ = stack[3].m_obj;
lean_object* v_res_3489_;
v_res_3489_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_stx_3446_, v_cfg_3447_, v_a_3448_, v_a_3449_);
stack->m_obj
 = v_res_3489_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___boxed(lean_object* v_stx_3490_, lean_object* v_cfg_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_stx_3490_, v_cfg_3491_, v_a_3492_, v_a_3493_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec_ref(v_cfg_3491_);
return v_res_3495_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3511_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3508_, v___x_3509_, v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3512_;
v_res_3512_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3512_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2____boxed(lean_object* v_a_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_();
return v_res_3514_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3532_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3535_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3532_, v___x_3533_, v___x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3536_;
v_res_3536_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3536_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2____boxed(lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
return v_res_3538_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3548_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3551_ = l_Lean_Meta_registerSimpAttr(v___x_3548_, v___x_3549_, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3552_;
v_res_3552_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3552_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2____boxed(lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
return v_res_3554_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(lean_object* v_e_3555_){
_start:
{
if (lean_obj_tag(v_e_3555_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3565_; 
v_a_3557_ = lean_ctor_get(v_e_3555_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_e_3555_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3559_ = v_e_3555_;
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v_e_3555_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3561_ = lean_mk_io_user_error(v_a_3557_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set_tag(v___x_3559_, 1);
lean_ctor_set(v___x_3559_, 0, v___x_3561_);
v___x_3563_ = v___x_3559_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
v_a_3566_ = lean_ctor_get(v_e_3555_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_e_3555_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v_e_3555_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v_e_3555_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
lean_ctor_set_tag(v___x_3568_, 0);
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3555_ = stack[0].m_obj;
lean_object* v_res_3574_;
v_res_3574_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3555_);
stack->m_obj
 = v_res_3574_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_e_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3575_);
return v_res_3577_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3578_, lean_object* v_e_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3579_ = stack[1].m_obj;
lean_object* v_res_3582_;
v_res_3582_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(lean_box(0), v_e_3579_);
stack->m_obj
 = v_res_3582_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3583_, lean_object* v_e_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(v_00_u03b1_3583_, v_e_3584_);
return v_res_3586_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v_declName_3587_, lean_object* v_stx_3588_, uint8_t v_attrKind_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; lean_object* v_env_3594_; lean_object* v_ref_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3593_ = lean_st_ref_get(v___y_3591_);
v_env_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_ref_n(v_env_3594_, 2);
lean_dec(v___x_3593_);
v_ref_3595_ = lean_ctor_get(v___y_3590_, 2);
v___x_3596_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3597_ = l_Lean_getAttributeImpl(v_env_3594_, v___x_3596_);
v___x_3598_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v_add_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v_add_3600_ = lean_ctor_get(v_a_3599_, 1);
lean_inc_ref(v_add_3600_);
lean_dec(v_a_3599_);
v___x_3601_ = lean_box(v_attrKind_3589_);
lean_inc(v___y_3591_);
lean_inc_ref(v___y_3590_);
lean_inc(v_stx_3588_);
lean_inc(v_declName_3587_);
v___x_3602_ = lean_apply_6(v_add_3600_, v_declName_3587_, v_stx_3588_, v___x_3601_, v___y_3590_, v___y_3591_, lean_box(0));
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3627_; 
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; 
v_unused_3628_ = lean_ctor_get(v___x_3602_, 0);
lean_dec(v_unused_3628_);
v___x_3604_ = v___x_3602_;
v_isShared_3605_ = v_isSharedCheck_3627_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v___x_3602_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3627_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3606_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3607_ = l_Lean_getAttributeImpl(v_env_3594_, v___x_3606_);
v___x_3608_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3607_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v_add_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
lean_del_object(v___x_3604_);
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v_add_3610_ = lean_ctor_get(v_a_3609_, 1);
lean_inc_ref(v_add_3610_);
lean_dec(v_a_3609_);
v___x_3611_ = lean_box(v_attrKind_3589_);
lean_inc(v___y_3591_);
lean_inc_ref(v___y_3590_);
v___x_3612_ = lean_apply_6(v_add_3610_, v_declName_3587_, v_stx_3588_, v___x_3611_, v___y_3590_, v___y_3591_, lean_box(0));
return v___x_3612_;
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3626_; 
lean_dec(v_stx_3588_);
lean_dec(v_declName_3587_);
v_a_3613_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3615_ = v___x_3608_;
v_isShared_3616_ = v_isSharedCheck_3626_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3608_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3626_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3617_ = lean_io_error_to_string(v_a_3613_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 3);
lean_ctor_set(v___x_3604_, 0, v___x_3617_);
v___x_3619_ = v___x_3604_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v___x_3620_ = l_Lean_MessageData_ofFormat(v___x_3619_);
lean_inc(v_ref_3595_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v_ref_3595_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3621_);
v___x_3623_ = v___x_3615_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_env_3594_);
lean_dec(v_stx_3588_);
lean_dec(v_declName_3587_);
return v___x_3602_;
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3640_; 
lean_dec_ref(v_env_3594_);
lean_dec(v_stx_3588_);
lean_dec(v_declName_3587_);
v_a_3629_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3631_ = v___x_3598_;
v_isShared_3632_ = v_isSharedCheck_3640_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3598_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3640_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3633_ = lean_io_error_to_string(v_a_3629_);
v___x_3634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
v___x_3635_ = l_Lean_MessageData_ofFormat(v___x_3634_);
lean_inc(v_ref_3595_);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v_ref_3595_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3636_);
v___x_3638_ = v___x_3631_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3587_ = stack[0].m_obj;
lean_object* v_stx_3588_ = stack[1].m_obj;
uint8_t v_attrKind_3589_ = stack[2].m_num;
lean_object* v___y_3590_ = stack[3].m_obj;
lean_object* v___y_3591_ = stack[4].m_obj;
lean_object* v_res_3641_;
v_res_3641_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v_declName_3587_, v_stx_3588_, v_attrKind_3589_, v___y_3590_, v___y_3591_);
stack->m_obj
 = v_res_3641_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_declName_3642_, lean_object* v_stx_3643_, lean_object* v_attrKind_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
uint8_t v_attrKind_boxed_3648_; lean_object* v_res_3649_; 
v_attrKind_boxed_3648_ = lean_unbox(v_attrKind_3644_);
v_res_3649_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v_declName_3642_, v_stx_3643_, v_attrKind_boxed_3648_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3652_ = l_Lean_stringToMessageData(v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v___x_3656_, lean_object* v_decl_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3662_ = l_Lean_MessageData_ofName(v___x_3656_);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3663_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v___x_3665_, v___y_3658_, v___y_3659_);
return v___x_3666_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3656_ = stack[0].m_obj;
lean_object* v_decl_3657_ = stack[1].m_obj;
lean_object* v___y_3658_ = stack[2].m_obj;
lean_object* v___y_3659_ = stack[3].m_obj;
lean_object* v_res_3667_;
v_res_3667_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v___x_3656_, v_decl_3657_, v___y_3658_, v___y_3659_);
stack->m_obj
 = v_res_3667_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v___x_3668_, lean_object* v_decl_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v___x_3668_, v_decl_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v_decl_3669_);
return v_res_3673_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3704_ = l_Lean_registerBuiltinAttribute(v___x_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3705_;
v_res_3705_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3705_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_a_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
return v_res_3707_;
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
