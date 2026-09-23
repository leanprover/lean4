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
lean_object* v___x_376_; lean_object* v_env_377_; lean_object* v___x_378_; lean_object* v_toCold_379_; lean_object* v_mctx_380_; lean_object* v_lctx_381_; lean_object* v_options_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_376_ = lean_st_ref_get(v___y_374_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc_ref(v_env_377_);
lean_dec(v___x_376_);
v___x_378_ = lean_st_ref_get(v___y_372_);
v_toCold_379_ = lean_ctor_get(v___y_373_, 0);
v_mctx_380_ = lean_ctor_get(v___x_378_, 0);
lean_inc_ref(v_mctx_380_);
lean_dec(v___x_378_);
v_lctx_381_ = lean_ctor_get(v___y_371_, 2);
v_options_382_ = lean_ctor_get(v_toCold_379_, 2);
lean_inc_ref(v_options_382_);
lean_inc_ref(v_lctx_381_);
v___x_383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_383_, 0, v_env_377_);
lean_ctor_set(v___x_383_, 1, v_mctx_380_);
lean_ctor_set(v___x_383_, 2, v_lctx_381_);
lean_ctor_set(v___x_383_, 3, v_options_382_);
v___x_384_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_msgData_370_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msgData_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_ref_399_; lean_object* v___x_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_ref_399_ = lean_ctor_get(v___y_396_, 2);
v___x_400_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
lean_inc(v_ref_399_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_ref_399_);
lean_ctor_set(v___x_405_, 1, v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__0));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(lean_object* v_ctor_420_, lean_object* v_args_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__0));
v___x_440_ = lean_string_dec_eq(v_ctor_420_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__1));
v___x_442_ = lean_string_dec_eq(v_ctor_420_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___lam__0___closed__2));
v___x_444_ = lean_string_dec_eq(v_ctor_420_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_array_get_size(v_args_421_);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_nat_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v___x_449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_450_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_449_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
goto v___jp_427_;
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_array_get_size(v_args_421_);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_nat_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v___x_462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_463_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_462_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
goto v___jp_431_;
}
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_array_get_size(v_args_421_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_nat_dec_eq(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v___x_475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_476_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_475_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
goto v___jp_435_;
}
}
v___jp_427_:
{
uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = 0;
v___x_429_ = lean_box(v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
v___jp_431_:
{
uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = 2;
v___x_433_ = lean_box(v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
v___jp_435_:
{
uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = 1;
v___x_437_ = lean_box(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___boxed(lean_object* v_ctor_485_, lean_object* v_args_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0(v_ctor_485_, v_args_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_args_486_);
lean_dec_ref(v_ctor_485_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___f_500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___closed__0));
v___x_501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm___closed__3));
v___x_502_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_501_, v___f_500_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___boxed(lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(lean_object* v_00_u03b1_510_, lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_518_, lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1(v_00_u03b1_518_, v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__0));
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__2);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(lean_object* v___x_534_, lean_object* v_ctor_535_, lean_object* v_args_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___closed__0));
v___x_719_ = lean_string_dec_eq(v_ctor_535_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__0___redArg();
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = lean_array_get_size(v_args_536_);
v___x_722_ = lean_unsigned_to_nat(13u);
v___x_723_ = lean_nat_dec_eq(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v___x_724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr___lam__0___closed__1);
v___x_725_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1___redArg(v___x_724_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
goto v___jp_542_;
}
}
v___jp_542_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_543_);
lean_inc(v___x_544_);
v___x_545_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_544_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_547_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_548_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = lean_unsigned_to_nat(2u);
v___x_552_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_551_);
lean_inc(v___x_552_);
v___x_553_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_552_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = lean_unsigned_to_nat(3u);
v___x_556_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_555_);
lean_inc(v___x_556_);
v___x_557_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_556_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = lean_unsigned_to_nat(4u);
v___x_560_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_559_);
lean_inc(v___x_560_);
v___x_561_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_560_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = lean_unsigned_to_nat(5u);
v___x_564_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_563_);
lean_inc(v___x_564_);
v___x_565_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_564_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = lean_unsigned_to_nat(6u);
v___x_568_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_567_);
lean_inc(v___x_568_);
v___x_569_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_568_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = lean_unsigned_to_nat(7u);
v___x_572_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_571_);
lean_inc(v___x_572_);
v___x_573_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_572_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = lean_unsigned_to_nat(8u);
v___x_576_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_575_);
lean_inc(v___x_576_);
v___x_577_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_576_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
v___x_579_ = lean_unsigned_to_nat(9u);
v___x_580_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_579_);
lean_inc(v___x_580_);
v___x_581_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_580_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = lean_unsigned_to_nat(10u);
v___x_584_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_583_);
lean_inc(v___x_584_);
v___x_585_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v___x_584_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = lean_unsigned_to_nat(11u);
v___x_588_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_587_);
lean_inc(v___x_588_);
v___x_589_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_588_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_unsigned_to_nat(12u);
v___x_592_ = lean_array_get_borrowed(v___x_534_, v_args_536_, v___x_591_);
lean_inc(v___x_592_);
v___x_593_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v___x_592_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_613_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_613_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; uint8_t v___x_599_; uint8_t v___x_600_; uint8_t v___x_601_; uint8_t v___x_602_; uint8_t v___x_603_; uint8_t v___x_604_; uint8_t v___x_605_; uint8_t v___x_606_; uint8_t v___x_607_; uint8_t v___x_608_; uint8_t v___x_609_; lean_object* v___x_611_; 
v___x_598_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_598_, 0, v_a_546_);
lean_ctor_set(v___x_598_, 1, v_a_586_);
v___x_599_ = lean_unbox(v_a_550_);
lean_dec(v_a_550_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2, v___x_599_);
v___x_600_ = lean_unbox(v_a_554_);
lean_dec(v_a_554_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 1, v___x_600_);
v___x_601_ = lean_unbox(v_a_558_);
lean_dec(v_a_558_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 2, v___x_601_);
v___x_602_ = lean_unbox(v_a_562_);
lean_dec(v_a_562_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 3, v___x_602_);
v___x_603_ = lean_unbox(v_a_566_);
lean_dec(v_a_566_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 4, v___x_603_);
v___x_604_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 5, v___x_604_);
v___x_605_ = lean_unbox(v_a_574_);
lean_dec(v_a_574_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 6, v___x_605_);
v___x_606_ = lean_unbox(v_a_578_);
lean_dec(v_a_578_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 7, v___x_606_);
v___x_607_ = lean_unbox(v_a_582_);
lean_dec(v_a_582_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 8, v___x_607_);
v___x_608_ = lean_unbox(v_a_590_);
lean_dec(v_a_590_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 9, v___x_608_);
v___x_609_ = lean_unbox(v_a_594_);
lean_dec(v_a_594_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*2 + 10, v___x_609_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_611_ = v___x_596_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_598_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_a_590_);
lean_dec(v_a_586_);
lean_dec(v_a_582_);
lean_dec(v_a_578_);
lean_dec(v_a_574_);
lean_dec(v_a_570_);
lean_dec(v_a_566_);
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_614_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_593_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_593_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v_a_586_);
lean_dec(v_a_582_);
lean_dec(v_a_578_);
lean_dec(v_a_574_);
lean_dec(v_a_570_);
lean_dec(v_a_566_);
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_622_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_589_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_589_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_582_);
lean_dec(v_a_578_);
lean_dec(v_a_574_);
lean_dec(v_a_570_);
lean_dec(v_a_566_);
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_630_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_585_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_585_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v_a_578_);
lean_dec(v_a_574_);
lean_dec(v_a_570_);
lean_dec(v_a_566_);
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_638_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_581_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_581_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_574_);
lean_dec(v_a_570_);
lean_dec(v_a_566_);
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_646_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_577_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_577_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_a_570_);
lean_dec(v_a_566_);
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_654_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_573_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_573_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_a_566_);
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_662_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_569_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_569_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_a_562_);
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_670_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_565_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_565_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec(v_a_558_);
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_678_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_561_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_561_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec(v_a_554_);
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_686_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_557_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_557_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_a_550_);
lean_dec(v_a_546_);
v_a_694_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_553_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_553_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_a_546_);
v_a_702_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_549_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_549_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
v_a_710_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_545_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_545_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed(lean_object* v___x_734_, lean_object* v_ctor_735_, lean_object* v_args_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0(v___x_734_, v_ctor_735_, v_args_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_args_736_);
lean_dec_ref(v_ctor_735_);
lean_dec_ref(v___x_734_);
return v_res_742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_743_; lean_object* v___f_744_; 
v___x_743_ = l_Lean_instInhabitedExpr;
v___f_744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___lam__0___boxed), 8, 1);
lean_closure_set(v___f_744_, 0, v___x_743_);
return v___f_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___f_758_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__0);
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_760_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_759_, v___f_758_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___boxed(lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_box(0);
v___x_770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_771_ = l_Lean_Expr_const___override(v___x_770_, v___x_769_);
return v___x_771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__0));
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig(void){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__3);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_box(0);
v___x_779_ = l_Lean_Elab_abortTermExceptionId;
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg(){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___closed__0);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg___boxed(lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v_res_785_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_box(1);
v___x_787_ = l_Lean_MessageData_ofFormat(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__2));
v___x_792_ = l_Lean_MessageData_ofFormat(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
return v_x_793_;
}
else
{
lean_object* v_head_795_; lean_object* v_tail_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_818_; 
v_head_795_ = lean_ctor_get(v_x_794_, 0);
v_tail_796_ = lean_ctor_get(v_x_794_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_818_ == 0)
{
v___x_798_ = v_x_794_;
v_isShared_799_ = v_isSharedCheck_818_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_tail_796_);
lean_inc(v_head_795_);
lean_dec(v_x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_818_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_before_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_816_; 
v_before_800_ = lean_ctor_get(v_head_795_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_head_795_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_head_795_, 1);
lean_dec(v_unused_817_);
v___x_802_ = v_head_795_;
v_isShared_803_ = v_isSharedCheck_816_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_before_800_);
lean_dec(v_head_795_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_816_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 7);
lean_ctor_set(v___x_802_, 1, v___x_804_);
lean_ctor_set(v___x_802_, 0, v_x_793_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_x_793_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_815_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__3);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 7);
lean_ctor_set(v___x_798_, 1, v___x_807_);
lean_ctor_set(v___x_798_, 0, v___x_806_);
v___x_809_ = v___x_798_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_807_);
v___x_809_ = v_reuseFailAlloc_814_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_810_ = l_Lean_MessageData_ofSyntax(v_before_800_);
v___x_811_ = l_Lean_indentD(v___x_810_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_809_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v_x_793_ = v___x_812_;
v_x_794_ = v_tail_796_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(lean_object* v_opts_819_, lean_object* v_opt_820_){
_start:
{
lean_object* v_name_821_; lean_object* v_defValue_822_; lean_object* v_map_823_; lean_object* v___x_824_; 
v_name_821_ = lean_ctor_get(v_opt_820_, 0);
v_defValue_822_ = lean_ctor_get(v_opt_820_, 1);
v_map_823_ = lean_ctor_get(v_opts_819_, 0);
v___x_824_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_823_, v_name_821_);
if (lean_obj_tag(v___x_824_) == 0)
{
uint8_t v___x_825_; 
v___x_825_ = lean_unbox(v_defValue_822_);
return v___x_825_;
}
else
{
lean_object* v_val_826_; 
v_val_826_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_824_, 1);
if (lean_obj_tag(v_val_826_) == 1)
{
uint8_t v_v_827_; 
v_v_827_ = lean_ctor_get_uint8(v_val_826_, 0);
lean_dec_ref_known(v_val_826_, 0);
return v_v_827_;
}
else
{
uint8_t v___x_828_; 
lean_dec(v_val_826_);
v___x_828_ = lean_unbox(v_defValue_822_);
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8___boxed(lean_object* v_opts_829_, lean_object* v_opt_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_opts_829_, v_opt_830_);
lean_dec_ref(v_opt_830_);
lean_dec_ref(v_opts_829_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__1));
v___x_837_ = l_Lean_MessageData_ofFormat(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(lean_object* v_msgData_838_, lean_object* v_macroStack_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_toCold_842_; lean_object* v_options_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_toCold_842_ = lean_ctor_get(v___y_840_, 0);
v_options_843_ = lean_ctor_get(v_toCold_842_, 2);
v___x_844_ = l_Lean_Elab_pp_macroStack;
v___x_845_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__8(v_options_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec(v_macroStack_839_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_msgData_838_);
return v___x_846_;
}
else
{
if (lean_obj_tag(v_macroStack_839_) == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_msgData_838_);
return v___x_847_;
}
else
{
lean_object* v_head_848_; lean_object* v_after_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_864_; 
v_head_848_ = lean_ctor_get(v_macroStack_839_, 0);
lean_inc(v_head_848_);
v_after_849_ = lean_ctor_get(v_head_848_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_head_848_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v_head_848_, 0);
lean_dec(v_unused_865_);
v___x_851_ = v_head_848_;
v_isShared_852_ = v_isSharedCheck_864_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_after_849_);
lean_dec(v_head_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_864_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9___closed__0);
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 7);
lean_ctor_set(v___x_851_, 1, v___x_853_);
lean_ctor_set(v___x_851_, 0, v_msgData_838_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_msgData_838_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_863_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_msgData_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_856_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___closed__2);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_MessageData_ofSyntax(v_after_849_);
v___x_859_ = l_Lean_indentD(v___x_858_);
v_msgData_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_860_, 0, v___x_857_);
lean_ctor_set(v_msgData_860_, 1, v___x_859_);
v___x_861_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6_spec__9(v_msgData_860_, v_macroStack_839_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_msgData_866_, lean_object* v_macroStack_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_866_, v_macroStack_867_, v___y_868_);
lean_dec_ref(v___y_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(lean_object* v_msg_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_ref_879_; lean_object* v_macroStack_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
v_ref_879_ = lean_ctor_get(v___y_876_, 2);
v_macroStack_880_ = lean_ctor_get(v___y_872_, 1);
v___x_881_ = l_Lean_Elab_getBetterRef(v_ref_879_, v_macroStack_880_);
v___x_882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr_spec__1_spec__1(v_msg_871_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
lean_inc(v_macroStack_880_);
v___x_884_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_a_883_, v_macroStack_880_, v___y_876_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_881_);
lean_ctor_set(v___x_889_, 1, v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 1);
lean_ctor_set(v___x_887_, 0, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg___boxed(lean_object* v_msg_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(lean_object* v_e_903_, lean_object* v___y_904_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = l_Lean_Expr_hasMVar(v_e_903_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_e_903_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v_mctx_909_; lean_object* v___x_910_; lean_object* v_fst_911_; lean_object* v_snd_912_; lean_object* v___x_913_; lean_object* v_cache_914_; lean_object* v_zetaDeltaFVarIds_915_; lean_object* v_postponed_916_; lean_object* v_diag_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_926_; 
v___x_908_ = lean_st_ref_get(v___y_904_);
v_mctx_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_mctx_909_);
lean_dec(v___x_908_);
v___x_910_ = l_Lean_instantiateMVarsCore(v_mctx_909_, v_e_903_);
v_fst_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_fst_911_);
v_snd_912_ = lean_ctor_get(v___x_910_, 1);
lean_inc(v_snd_912_);
lean_dec_ref(v___x_910_);
v___x_913_ = lean_st_ref_take(v___y_904_);
v_cache_914_ = lean_ctor_get(v___x_913_, 1);
v_zetaDeltaFVarIds_915_ = lean_ctor_get(v___x_913_, 2);
v_postponed_916_ = lean_ctor_get(v___x_913_, 3);
v_diag_917_ = lean_ctor_get(v___x_913_, 4);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v___x_913_, 0);
lean_dec(v_unused_927_);
v___x_919_ = v___x_913_;
v_isShared_920_ = v_isSharedCheck_926_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_diag_917_);
lean_inc(v_postponed_916_);
lean_inc(v_zetaDeltaFVarIds_915_);
lean_inc(v_cache_914_);
lean_dec(v___x_913_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_926_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v_snd_912_);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_snd_912_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_cache_914_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_zetaDeltaFVarIds_915_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_postponed_916_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_diag_917_);
v___x_922_ = v_reuseFailAlloc_925_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_st_ref_put(v___y_904_, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_fst_911_);
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg___boxed(lean_object* v_e_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_928_, v___y_929_);
lean_dec(v___y_929_);
return v_res_931_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__1);
v___x_936_ = l_Lean_MessageData_ofExpr(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__2);
v___x_938_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__4));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_944_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__3);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__7));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__9));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(lean_object* v_stx_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_ty_x3f_960_; uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_toCold_966_; lean_object* v_currRecDepth_967_; lean_object* v_ref_968_; uint8_t v_diag_969_; uint8_t v_suppressElabErrors_970_; uint8_t v___x_971_; lean_object* v_ref_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_ty_x3f_960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig___closed__2);
v___x_961_ = 1;
v___x_962_ = lean_box(0);
v___x_963_ = lean_box(v___x_961_);
v___x_964_ = lean_box(v___x_961_);
lean_inc(v_stx_952_);
v___x_965_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_965_, 0, v_stx_952_);
lean_closure_set(v___x_965_, 1, v_ty_x3f_960_);
lean_closure_set(v___x_965_, 2, v___x_963_);
lean_closure_set(v___x_965_, 3, v___x_964_);
lean_closure_set(v___x_965_, 4, v___x_962_);
v_toCold_966_ = lean_ctor_get(v_a_957_, 0);
v_currRecDepth_967_ = lean_ctor_get(v_a_957_, 1);
v_ref_968_ = lean_ctor_get(v_a_957_, 2);
v_diag_969_ = lean_ctor_get_uint8(v_a_957_, sizeof(void*)*3);
v_suppressElabErrors_970_ = lean_ctor_get_uint8(v_a_957_, sizeof(void*)*3 + 1);
v___x_971_ = 1;
v_ref_972_ = l_Lean_replaceRef(v_stx_952_, v_ref_968_);
lean_dec(v_stx_952_);
lean_inc(v_currRecDepth_967_);
lean_inc_ref(v_toCold_966_);
v___x_973_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_973_, 0, v_toCold_966_);
lean_ctor_set(v___x_973_, 1, v_currRecDepth_967_);
lean_ctor_set(v___x_973_, 2, v_ref_972_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*3, v_diag_969_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*3 + 1, v_suppressElabErrors_970_);
v___x_974_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_965_, v___x_971_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v___x_973_, v_a_958_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; uint8_t v___y_988_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; uint8_t v___x_1072_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_975_, v_a_956_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref(v___x_976_);
v___x_1072_ = l_Lean_Expr_hasSorry(v_a_977_);
if (v___x_1072_ == 0)
{
v___y_1017_ = v_a_953_;
v___y_1018_ = v_a_954_;
v___y_1019_ = v_a_955_;
v___y_1020_ = v_a_956_;
v___y_1021_ = v___x_973_;
v___y_1022_ = v_a_958_;
goto v___jp_1016_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_Expr_hasSyntheticSorry(v_a_977_);
if (v___x_1073_ == 0)
{
v___y_1054_ = v_a_953_;
v___y_1055_ = v_a_954_;
v___y_1056_ = v_a_955_;
v___y_1057_ = v_a_956_;
v___y_1058_ = v___x_973_;
v___y_1059_ = v_a_958_;
goto v___jp_1053_;
}
else
{
lean_object* v___x_1074_; lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_a_977_);
lean_dec_ref_known(v___x_973_, 3);
v___x_1074_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
v___jp_978_:
{
if (v___y_988_ == 0)
{
if (lean_obj_tag(v___y_981_) == 0)
{
lean_dec_ref_known(v___y_981_, 2);
lean_dec_ref(v___y_986_);
lean_dec(v_a_977_);
return v___y_982_;
}
else
{
lean_object* v_id_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1002_; 
v_id_989_ = lean_ctor_get(v___y_981_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___y_981_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v___y_981_, 1);
lean_dec(v_unused_1003_);
v___x_991_ = v___y_981_;
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_id_989_);
lean_dec(v___y_981_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
uint8_t v___x_993_; 
v___x_993_ = l_Lean_instBEqInternalExceptionId_beq(v___y_983_, v_id_989_);
lean_dec(v_id_989_);
if (v___x_993_ == 0)
{
lean_del_object(v___x_991_);
lean_dec_ref(v___y_986_);
lean_dec(v_a_977_);
return v___y_982_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
lean_dec_ref(v___y_982_);
v___x_994_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__6);
v___x_995_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_996_ = l_Lean_indentExpr(v_a_977_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 7);
lean_ctor_set(v___x_991_, 1, v___x_996_);
lean_ctor_set(v___x_991_, 0, v___x_995_);
v___x_998_ = v___x_991_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_1001_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_994_);
v___x_1000_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_999_, v___y_979_, v___y_985_, v___y_987_, v___y_984_, v___y_986_, v___y_980_);
lean_dec_ref(v___y_986_);
return v___x_1000_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_986_);
lean_dec_ref(v___y_981_);
lean_dec(v_a_977_);
return v___y_982_;
}
}
v___jp_1004_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_977_);
v___x_1012_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr(v_a_977_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_dec_ref(v___y_1009_);
lean_dec(v_a_977_);
return v___x_1012_;
}
else
{
lean_object* v_a_1013_; uint8_t v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
v___x_1014_ = l_Lean_Exception_isInterrupt(v_a_1013_);
if (v___x_1014_ == 0)
{
uint8_t v___x_1015_; 
lean_inc(v_a_1013_);
v___x_1015_ = l_Lean_Exception_isRuntime(v_a_1013_);
v___y_979_ = v___y_1005_;
v___y_980_ = v___y_1010_;
v___y_981_ = v_a_1013_;
v___y_982_ = v___x_1012_;
v___y_983_ = v___x_1011_;
v___y_984_ = v___y_1008_;
v___y_985_ = v___y_1006_;
v___y_986_ = v___y_1009_;
v___y_987_ = v___y_1007_;
v___y_988_ = v___x_1015_;
goto v___jp_978_;
}
else
{
v___y_979_ = v___y_1005_;
v___y_980_ = v___y_1010_;
v___y_981_ = v_a_1013_;
v___y_982_ = v___x_1012_;
v___y_983_ = v___x_1011_;
v___y_984_ = v___y_1008_;
v___y_985_ = v___y_1006_;
v___y_986_ = v___y_1009_;
v___y_987_ = v___y_1007_;
v___y_988_ = v___x_1014_;
goto v___jp_978_;
}
}
}
v___jp_1016_:
{
lean_object* v___x_1023_; 
lean_inc(v_a_977_);
v___x_1023_ = l_Lean_Meta_getMVars(v_a_977_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1024_, v___x_962_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v_a_1024_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; uint8_t v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = lean_unbox(v_a_1026_);
lean_dec(v_a_1026_);
if (v___x_1027_ == 0)
{
v___y_1005_ = v___y_1017_;
v___y_1006_ = v___y_1018_;
v___y_1007_ = v___y_1019_;
v___y_1008_ = v___y_1020_;
v___y_1009_ = v___y_1021_;
v___y_1010_ = v___y_1022_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1028_; lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v___y_1021_);
lean_dec(v_a_977_);
v___x_1028_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v___y_1021_);
lean_dec(v_a_977_);
v_a_1037_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1025_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1025_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___y_1021_);
lean_dec(v_a_977_);
v_a_1045_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1023_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1023_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
v___jp_1053_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v___x_1060_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1061_ = l_Lean_indentExpr(v_a_977_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1062_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec_ref(v___y_1058_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref_known(v___x_973_, 3);
v_a_1083_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_974_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_974_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___boxed(lean_object* v_stx_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_stx_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode___closed__1);
v___x_1101_ = l_Lean_MessageData_ofExpr(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__0);
v___x_1103_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1106_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__1);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v___x_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(lean_object* v_stx_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_ty_x3f_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_toCold_1122_; lean_object* v_currRecDepth_1123_; lean_object* v_ref_1124_; uint8_t v_diag_1125_; uint8_t v_suppressElabErrors_1126_; uint8_t v___x_1127_; lean_object* v_ref_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_ty_x3f_1116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode___closed__1);
v___x_1117_ = 1;
v___x_1118_ = lean_box(0);
v___x_1119_ = lean_box(v___x_1117_);
v___x_1120_ = lean_box(v___x_1117_);
lean_inc(v_stx_1108_);
v___x_1121_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1121_, 0, v_stx_1108_);
lean_closure_set(v___x_1121_, 1, v_ty_x3f_1116_);
lean_closure_set(v___x_1121_, 2, v___x_1119_);
lean_closure_set(v___x_1121_, 3, v___x_1120_);
lean_closure_set(v___x_1121_, 4, v___x_1118_);
v_toCold_1122_ = lean_ctor_get(v_a_1113_, 0);
v_currRecDepth_1123_ = lean_ctor_get(v_a_1113_, 1);
v_ref_1124_ = lean_ctor_get(v_a_1113_, 2);
v_diag_1125_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*3);
v_suppressElabErrors_1126_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*3 + 1);
v___x_1127_ = 1;
v_ref_1128_ = l_Lean_replaceRef(v_stx_1108_, v_ref_1124_);
lean_dec(v_stx_1108_);
lean_inc(v_currRecDepth_1123_);
lean_inc_ref(v_toCold_1122_);
v___x_1129_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1129_, 0, v_toCold_1122_);
lean_ctor_set(v___x_1129_, 1, v_currRecDepth_1123_);
lean_ctor_set(v___x_1129_, 2, v_ref_1128_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*3, v_diag_1125_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*3 + 1, v_suppressElabErrors_1126_);
v___x_1130_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1121_, v___x_1127_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v___x_1129_, v_a_1114_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; lean_object* v_a_1133_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v___y_1144_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; uint8_t v___x_1228_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1131_, v_a_1112_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1132_);
v___x_1228_ = l_Lean_Expr_hasSorry(v_a_1133_);
if (v___x_1228_ == 0)
{
v___y_1173_ = v_a_1109_;
v___y_1174_ = v_a_1110_;
v___y_1175_ = v_a_1111_;
v___y_1176_ = v_a_1112_;
v___y_1177_ = v___x_1129_;
v___y_1178_ = v_a_1114_;
goto v___jp_1172_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = l_Lean_Expr_hasSyntheticSorry(v_a_1133_);
if (v___x_1229_ == 0)
{
v___y_1210_ = v_a_1109_;
v___y_1211_ = v_a_1110_;
v___y_1212_ = v_a_1111_;
v___y_1213_ = v_a_1112_;
v___y_1214_ = v___x_1129_;
v___y_1215_ = v_a_1114_;
goto v___jp_1209_;
}
else
{
lean_object* v___x_1230_; lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_a_1133_);
lean_dec_ref_known(v___x_1129_, 3);
v___x_1230_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
v___jp_1134_:
{
if (v___y_1144_ == 0)
{
if (lean_obj_tag(v___y_1137_) == 0)
{
lean_dec_ref_known(v___y_1137_, 2);
lean_dec_ref(v___y_1141_);
lean_dec(v_a_1133_);
return v___y_1139_;
}
else
{
lean_object* v_id_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1158_; 
v_id_1145_ = lean_ctor_get(v___y_1137_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___y_1137_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v___y_1137_, 1);
lean_dec(v_unused_1159_);
v___x_1147_ = v___y_1137_;
v_isShared_1148_ = v_isSharedCheck_1158_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_id_1145_);
lean_dec(v___y_1137_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1158_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
uint8_t v___x_1149_; 
v___x_1149_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1140_, v_id_1145_);
lean_dec(v_id_1145_);
if (v___x_1149_ == 0)
{
lean_del_object(v___x_1147_);
lean_dec_ref(v___y_1141_);
lean_dec(v_a_1133_);
return v___y_1139_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_dec_ref(v___y_1139_);
v___x_1150_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___closed__2);
v___x_1151_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1152_ = l_Lean_indentExpr(v_a_1133_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 7);
lean_ctor_set(v___x_1147_, 1, v___x_1152_);
lean_ctor_set(v___x_1147_, 0, v___x_1151_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1150_);
v___x_1156_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1155_, v___y_1143_, v___y_1142_, v___y_1138_, v___y_1135_, v___y_1141_, v___y_1136_);
lean_dec_ref(v___y_1141_);
return v___x_1156_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1141_);
lean_dec_ref(v___y_1137_);
lean_dec(v_a_1133_);
return v___y_1139_;
}
}
v___jp_1160_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1133_);
v___x_1168_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprSolverMode_evalExpr(v_a_1133_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_dec_ref(v___y_1165_);
lean_dec(v_a_1133_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; uint8_t v___x_1170_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
v___x_1170_ = l_Lean_Exception_isInterrupt(v_a_1169_);
if (v___x_1170_ == 0)
{
uint8_t v___x_1171_; 
lean_inc(v_a_1169_);
v___x_1171_ = l_Lean_Exception_isRuntime(v_a_1169_);
v___y_1135_ = v___y_1164_;
v___y_1136_ = v___y_1166_;
v___y_1137_ = v_a_1169_;
v___y_1138_ = v___y_1163_;
v___y_1139_ = v___x_1168_;
v___y_1140_ = v___x_1167_;
v___y_1141_ = v___y_1165_;
v___y_1142_ = v___y_1162_;
v___y_1143_ = v___y_1161_;
v___y_1144_ = v___x_1171_;
goto v___jp_1134_;
}
else
{
v___y_1135_ = v___y_1164_;
v___y_1136_ = v___y_1166_;
v___y_1137_ = v_a_1169_;
v___y_1138_ = v___y_1163_;
v___y_1139_ = v___x_1168_;
v___y_1140_ = v___x_1167_;
v___y_1141_ = v___y_1165_;
v___y_1142_ = v___y_1162_;
v___y_1143_ = v___y_1161_;
v___y_1144_ = v___x_1170_;
goto v___jp_1134_;
}
}
}
v___jp_1172_:
{
lean_object* v___x_1179_; 
lean_inc(v_a_1133_);
v___x_1179_ = l_Lean_Meta_getMVars(v_a_1133_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1181_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1181_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1180_, v___x_1118_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v_a_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; uint8_t v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = lean_unbox(v_a_1182_);
lean_dec(v_a_1182_);
if (v___x_1183_ == 0)
{
v___y_1161_ = v___y_1173_;
v___y_1162_ = v___y_1174_;
v___y_1163_ = v___y_1175_;
v___y_1164_ = v___y_1176_;
v___y_1165_ = v___y_1177_;
v___y_1166_ = v___y_1178_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1184_; lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v___y_1177_);
lean_dec(v_a_1133_);
v___x_1184_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
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
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v___y_1177_);
lean_dec(v_a_1133_);
v_a_1193_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1181_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1181_);
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
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v___y_1177_);
lean_dec(v_a_1133_);
v_a_1201_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1179_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1179_);
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
v___jp_1209_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v___x_1216_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1217_ = l_Lean_indentExpr(v_a_1133_);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1218_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec_ref(v___y_1214_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref_known(v___x_1129_, 3);
v_a_1239_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1130_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1130_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_stx_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(lean_object* v_stx_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_toCold_1264_; lean_object* v_currRecDepth_1265_; lean_object* v_ref_1266_; uint8_t v_diag_1267_; uint8_t v_suppressElabErrors_1268_; lean_object* v___x_1269_; lean_object* v_ref_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_toCold_1264_ = lean_ctor_get(v_a_1261_, 0);
v_currRecDepth_1265_ = lean_ctor_get(v_a_1261_, 1);
v_ref_1266_ = lean_ctor_get(v_a_1261_, 2);
v_diag_1267_ = lean_ctor_get_uint8(v_a_1261_, sizeof(void*)*3);
v_suppressElabErrors_1268_ = lean_ctor_get_uint8(v_a_1261_, sizeof(void*)*3 + 1);
v___x_1269_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1270_ = l_Lean_replaceRef(v_stx_1256_, v_ref_1266_);
lean_inc(v_currRecDepth_1265_);
lean_inc_ref(v_toCold_1264_);
v___x_1271_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1271_, 0, v_toCold_1264_);
lean_ctor_set(v___x_1271_, 1, v_currRecDepth_1265_);
lean_ctor_set(v___x_1271_, 2, v_ref_1270_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*3, v_diag_1267_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*3 + 1, v_suppressElabErrors_1268_);
lean_inc(v_stx_1256_);
v___x_1272_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalTermSolverMode_evalTerm(v_stx_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v___x_1271_, v_a_1262_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref_known(v___x_1271_, 3);
lean_dec(v_stx_1256_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_fst_1277_; lean_object* v___x_1279_; 
v_fst_1277_ = lean_ctor_get(v_a_1273_, 0);
lean_inc(v_fst_1277_);
lean_dec(v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v_fst_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_fst_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1296_; 
v_a_1282_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1284_ = v___x_1272_;
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1272_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
lean_inc(v_a_1282_);
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
uint8_t v___y_1289_; uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Exception_isInterrupt(v_a_1282_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
lean_inc(v_a_1282_);
v___x_1294_ = l_Lean_Exception_isRuntime(v_a_1282_);
v___y_1289_ = v___x_1294_;
goto v___jp_1288_;
}
else
{
v___y_1289_ = v___x_1293_;
goto v___jp_1288_;
}
v___jp_1288_:
{
if (v___y_1289_ == 0)
{
if (lean_obj_tag(v_a_1282_) == 0)
{
lean_dec_ref_known(v_a_1282_, 2);
lean_dec_ref_known(v___x_1271_, 3);
lean_dec(v_stx_1256_);
return v___x_1287_;
}
else
{
lean_object* v_id_1290_; uint8_t v___x_1291_; 
v_id_1290_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_id_1290_);
lean_dec_ref_known(v_a_1282_, 2);
v___x_1291_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1269_, v_id_1290_);
lean_dec(v_id_1290_);
if (v___x_1291_ == 0)
{
lean_dec_ref_known(v___x_1271_, 3);
lean_dec(v_stx_1256_);
return v___x_1287_;
}
else
{
lean_object* v___x_1292_; 
lean_dec_ref(v___x_1287_);
v___x_1292_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1_spec__2(v_stx_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v___x_1271_, v_a_1262_);
lean_dec_ref_known(v___x_1271_, 3);
return v___x_1292_;
}
}
}
else
{
lean_dec(v_a_1282_);
lean_dec_ref_known(v___x_1271_, 3);
lean_dec(v_stx_1256_);
return v___x_1287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_stx_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
return v_res_1305_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__1));
v___x_1311_ = l_Lean_mkConst(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1312_; lean_object* v_ty_x3f_1313_; 
v___x_1312_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v_ty_x3f_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_ty_x3f_1313_, 0, v___x_1312_);
return v_ty_x3f_1313_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__2);
v___x_1315_ = l_Lean_MessageData_ofExpr(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__4);
v___x_1317_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__1);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1316_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_1320_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v___x_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_ty_x3f_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_toCold_1336_; lean_object* v_currRecDepth_1337_; lean_object* v_ref_1338_; uint8_t v_diag_1339_; uint8_t v_suppressElabErrors_1340_; uint8_t v___x_1341_; lean_object* v_ref_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_ty_x3f_1330_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_1331_ = 1;
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_box(v___x_1331_);
v___x_1334_ = lean_box(v___x_1331_);
lean_inc(v_stx_1322_);
v___x_1335_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1335_, 0, v_stx_1322_);
lean_closure_set(v___x_1335_, 1, v_ty_x3f_1330_);
lean_closure_set(v___x_1335_, 2, v___x_1333_);
lean_closure_set(v___x_1335_, 3, v___x_1334_);
lean_closure_set(v___x_1335_, 4, v___x_1332_);
v_toCold_1336_ = lean_ctor_get(v_a_1327_, 0);
v_currRecDepth_1337_ = lean_ctor_get(v_a_1327_, 1);
v_ref_1338_ = lean_ctor_get(v_a_1327_, 2);
v_diag_1339_ = lean_ctor_get_uint8(v_a_1327_, sizeof(void*)*3);
v_suppressElabErrors_1340_ = lean_ctor_get_uint8(v_a_1327_, sizeof(void*)*3 + 1);
v___x_1341_ = 1;
v_ref_1342_ = l_Lean_replaceRef(v_stx_1322_, v_ref_1338_);
lean_dec(v_stx_1322_);
lean_inc(v_currRecDepth_1337_);
lean_inc_ref(v_toCold_1336_);
v___x_1343_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1343_, 0, v_toCold_1336_);
lean_ctor_set(v___x_1343_, 1, v_currRecDepth_1337_);
lean_ctor_set(v___x_1343_, 2, v_ref_1342_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*3, v_diag_1339_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*3 + 1, v_suppressElabErrors_1340_);
v___x_1344_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1335_, v___x_1341_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v___x_1343_, v_a_1328_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v_a_1347_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; uint8_t v___y_1358_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___x_1442_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_a_1345_, v_a_1326_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref(v___x_1346_);
v___x_1442_ = l_Lean_Expr_hasSorry(v_a_1347_);
if (v___x_1442_ == 0)
{
v___y_1387_ = v_a_1323_;
v___y_1388_ = v_a_1324_;
v___y_1389_ = v_a_1325_;
v___y_1390_ = v_a_1326_;
v___y_1391_ = v___x_1343_;
v___y_1392_ = v_a_1328_;
goto v___jp_1386_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_Expr_hasSyntheticSorry(v_a_1347_);
if (v___x_1443_ == 0)
{
v___y_1424_ = v_a_1323_;
v___y_1425_ = v_a_1324_;
v___y_1426_ = v_a_1325_;
v___y_1427_ = v_a_1326_;
v___y_1428_ = v___x_1343_;
v___y_1429_ = v_a_1328_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1444_; lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_a_1347_);
lean_dec_ref_known(v___x_1343_, 3);
v___x_1444_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
v___jp_1348_:
{
if (v___y_1358_ == 0)
{
if (lean_obj_tag(v___y_1356_) == 0)
{
lean_dec_ref_known(v___y_1356_, 2);
lean_dec_ref(v___y_1355_);
lean_dec(v_a_1347_);
return v___y_1349_;
}
else
{
lean_object* v_id_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1372_; 
v_id_1359_ = lean_ctor_get(v___y_1356_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___y_1356_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___y_1356_, 1);
lean_dec(v_unused_1373_);
v___x_1361_ = v___y_1356_;
v_isShared_1362_ = v_isSharedCheck_1372_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_id_1359_);
lean_dec(v___y_1356_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1372_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
uint8_t v___x_1363_; 
v___x_1363_ = l_Lean_instBEqInternalExceptionId_beq(v___y_1350_, v_id_1359_);
lean_dec(v_id_1359_);
if (v___x_1363_ == 0)
{
lean_del_object(v___x_1361_);
lean_dec_ref(v___y_1355_);
lean_dec(v_a_1347_);
return v___y_1349_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec_ref(v___y_1349_);
v___x_1364_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___closed__6);
v___x_1365_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__8);
v___x_1366_ = l_Lean_indentExpr(v_a_1347_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 7);
lean_ctor_set(v___x_1361_, 1, v___x_1366_);
lean_ctor_set(v___x_1361_, 0, v___x_1365_);
v___x_1368_ = v___x_1361_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v___x_1364_);
v___x_1370_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1369_, v___y_1357_, v___y_1352_, v___y_1353_, v___y_1351_, v___y_1355_, v___y_1354_);
lean_dec_ref(v___y_1355_);
return v___x_1370_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v_a_1347_);
return v___y_1349_;
}
}
v___jp_1374_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_1347_);
v___x_1382_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_a_1347_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_dec_ref(v___y_1379_);
lean_dec(v_a_1347_);
return v___x_1382_;
}
else
{
lean_object* v_a_1383_; uint8_t v___x_1384_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
v___x_1384_ = l_Lean_Exception_isInterrupt(v_a_1383_);
if (v___x_1384_ == 0)
{
uint8_t v___x_1385_; 
lean_inc(v_a_1383_);
v___x_1385_ = l_Lean_Exception_isRuntime(v_a_1383_);
v___y_1349_ = v___x_1382_;
v___y_1350_ = v___x_1381_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1376_;
v___y_1353_ = v___y_1377_;
v___y_1354_ = v___y_1380_;
v___y_1355_ = v___y_1379_;
v___y_1356_ = v_a_1383_;
v___y_1357_ = v___y_1375_;
v___y_1358_ = v___x_1385_;
goto v___jp_1348_;
}
else
{
v___y_1349_ = v___x_1382_;
v___y_1350_ = v___x_1381_;
v___y_1351_ = v___y_1378_;
v___y_1352_ = v___y_1376_;
v___y_1353_ = v___y_1377_;
v___y_1354_ = v___y_1380_;
v___y_1355_ = v___y_1379_;
v___y_1356_ = v_a_1383_;
v___y_1357_ = v___y_1375_;
v___y_1358_ = v___x_1384_;
goto v___jp_1348_;
}
}
}
v___jp_1386_:
{
lean_object* v___x_1393_; 
lean_inc(v_a_1347_);
v___x_1393_ = l_Lean_Meta_getMVars(v_a_1347_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1394_, v___x_1332_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v_a_1394_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; uint8_t v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = lean_unbox(v_a_1396_);
lean_dec(v_a_1396_);
if (v___x_1397_ == 0)
{
v___y_1375_ = v___y_1387_;
v___y_1376_ = v___y_1388_;
v___y_1377_ = v___y_1389_;
v___y_1378_ = v___y_1390_;
v___y_1379_ = v___y_1391_;
v___y_1380_ = v___y_1392_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1398_; lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v___y_1391_);
lean_dec(v_a_1347_);
v___x_1398_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v___y_1391_);
lean_dec(v_a_1347_);
v_a_1407_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1395_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1395_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
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
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___y_1391_);
lean_dec(v_a_1347_);
v_a_1415_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1393_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1393_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
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
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
v___jp_1423_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v___x_1430_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__10);
v___x_1431_ = l_Lean_indentExpr(v_a_1347_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v___x_1432_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec_ref(v___y_1428_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref_known(v___x_1343_, 3);
v_a_1453_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1344_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1344_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(lean_object* v_stx_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_toCold_1478_; lean_object* v_currRecDepth_1479_; lean_object* v_ref_1480_; uint8_t v_diag_1481_; uint8_t v_suppressElabErrors_1482_; lean_object* v___x_1483_; lean_object* v_ref_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_toCold_1478_ = lean_ctor_get(v_a_1475_, 0);
v_currRecDepth_1479_ = lean_ctor_get(v_a_1475_, 1);
v_ref_1480_ = lean_ctor_get(v_a_1475_, 2);
v_diag_1481_ = lean_ctor_get_uint8(v_a_1475_, sizeof(void*)*3);
v_suppressElabErrors_1482_ = lean_ctor_get_uint8(v_a_1475_, sizeof(void*)*3 + 1);
v___x_1483_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v_ref_1484_ = l_Lean_replaceRef(v_stx_1470_, v_ref_1480_);
lean_inc(v_currRecDepth_1479_);
lean_inc_ref(v_toCold_1478_);
v___x_1485_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1485_, 0, v_toCold_1478_);
lean_ctor_set(v___x_1485_, 1, v_currRecDepth_1479_);
lean_ctor_set(v___x_1485_, 2, v_ref_1484_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3, v_diag_1481_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 1, v_suppressElabErrors_1482_);
lean_inc(v_stx_1470_);
v___x_1486_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v___x_1485_, v_a_1476_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref_known(v___x_1485_, 3);
lean_dec(v_stx_1470_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_fst_1491_; lean_object* v___x_1493_; 
v_fst_1491_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_fst_1491_);
lean_dec(v_a_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v_fst_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_fst_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1510_; 
v_a_1496_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1498_ = v___x_1486_;
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1486_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1510_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
lean_inc(v_a_1496_);
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
uint8_t v___y_1503_; uint8_t v___x_1507_; 
v___x_1507_ = l_Lean_Exception_isInterrupt(v_a_1496_);
if (v___x_1507_ == 0)
{
uint8_t v___x_1508_; 
lean_inc(v_a_1496_);
v___x_1508_ = l_Lean_Exception_isRuntime(v_a_1496_);
v___y_1503_ = v___x_1508_;
goto v___jp_1502_;
}
else
{
v___y_1503_ = v___x_1507_;
goto v___jp_1502_;
}
v___jp_1502_:
{
if (v___y_1503_ == 0)
{
if (lean_obj_tag(v_a_1496_) == 0)
{
lean_dec_ref_known(v_a_1496_, 2);
lean_dec_ref_known(v___x_1485_, 3);
lean_dec(v_stx_1470_);
return v___x_1501_;
}
else
{
lean_object* v_id_1504_; uint8_t v___x_1505_; 
v_id_1504_ = lean_ctor_get(v_a_1496_, 0);
lean_inc(v_id_1504_);
lean_dec_ref_known(v_a_1496_, 2);
v___x_1505_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1483_, v_id_1504_);
lean_dec(v_id_1504_);
if (v___x_1505_ == 0)
{
lean_dec_ref_known(v___x_1485_, 3);
lean_dec(v_stx_1470_);
return v___x_1501_;
}
else
{
lean_object* v___x_1506_; 
lean_dec_ref(v___x_1501_);
v___x_1506_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0_spec__0(v_stx_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v___x_1485_, v_a_1476_);
lean_dec_ref_known(v___x_1485_, 3);
return v___x_1506_;
}
}
}
else
{
lean_dec(v_a_1496_);
lean_dec_ref_known(v___x_1485_, 3);
lean_dec(v_stx_1470_);
return v___x_1501_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_stx_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(lean_object* v_config_1627_, lean_object* v_item_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_item_1637_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_1641_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1628_, v___x_1640_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1641_) == 0)
{
uint8_t v___x_1642_; 
lean_dec_ref_known(v___x_1641_, 1);
v___x_1642_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1628_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1643_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1628_);
lean_inc_ref(v_item_1628_);
v___x_1644_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1628_);
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__1));
v___x_1646_ = lean_string_dec_lt(v___x_1643_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__2));
v___x_1648_ = lean_string_dec_lt(v___x_1643_, v___x_1647_);
if (v___x_1648_ == 0)
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_string_dec_eq(v___x_1643_, v___x_1647_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__3));
v___x_1651_ = lean_string_dec_eq(v___x_1643_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__4));
v___x_1653_ = lean_string_dec_eq(v___x_1643_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__5));
v___x_1655_ = lean_string_dec_eq(v___x_1643_, v___x_1654_);
lean_dec_ref(v___x_1643_);
if (v___x_1655_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__6));
v___x_1657_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_1656_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1657_) == 0)
{
uint8_t v___x_1658_; 
lean_dec_ref_known(v___x_1657_, 1);
v___x_1658_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_1658_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1659_; 
lean_dec_ref(v___x_1644_);
v___x_1659_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1687_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1687_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1687_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_timeout_1664_; uint8_t v_binaryProofs_1665_; uint8_t v_acNf_1666_; uint8_t v_andFlattening_1667_; uint8_t v_embeddedConstraintSubst_1668_; uint8_t v_structures_1669_; uint8_t v_fixedInt_1670_; uint8_t v_enums_1671_; uint8_t v_graphviz_1672_; lean_object* v_maxSteps_1673_; uint8_t v_shortCircuit_1674_; uint8_t v_solverMode_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1686_; 
v_timeout_1664_ = lean_ctor_get(v_config_1627_, 0);
v_binaryProofs_1665_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_1666_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_1667_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1668_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_1669_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_1670_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_1671_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_1672_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_1673_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_1674_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_1675_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1677_ = v_config_1627_;
v_isShared_1678_ = v_isSharedCheck_1686_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_maxSteps_1673_);
lean_inc(v_timeout_1664_);
lean_dec(v_config_1627_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1686_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_timeout_1664_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_maxSteps_1673_);
v___x_1680_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
uint8_t v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_unbox(v_a_1660_);
lean_dec(v_a_1660_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2, v___x_1681_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 1, v_binaryProofs_1665_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 2, v_acNf_1666_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 3, v_andFlattening_1667_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1668_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 5, v_structures_1669_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 6, v_fixedInt_1670_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 7, v_enums_1671_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 8, v_graphviz_1672_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 9, v_shortCircuit_1674_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*2 + 10, v_solverMode_1675_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1680_);
v___x_1683_ = v___x_1662_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1680_);
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
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v_config_1627_);
v_a_1688_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1659_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1659_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
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
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1696_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1657_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1657_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref(v___x_1643_);
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__7));
v___x_1705_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_1704_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1705_) == 0)
{
uint8_t v___x_1706_; 
lean_dec_ref_known(v___x_1705_, 1);
v___x_1706_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_1706_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1707_; 
lean_dec_ref(v___x_1644_);
lean_inc_ref(v_item_1628_);
v___x_1707_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_value_1708_; lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1707_, 1);
v_value_1708_ = lean_ctor_get(v_item_1628_, 2);
lean_inc(v_value_1708_);
lean_dec_ref(v_item_1628_);
v___x_1709_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1708_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1737_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1737_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1737_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
uint8_t v_trimProofs_1714_; uint8_t v_binaryProofs_1715_; uint8_t v_acNf_1716_; uint8_t v_andFlattening_1717_; uint8_t v_embeddedConstraintSubst_1718_; uint8_t v_structures_1719_; uint8_t v_fixedInt_1720_; uint8_t v_enums_1721_; uint8_t v_graphviz_1722_; lean_object* v_maxSteps_1723_; uint8_t v_shortCircuit_1724_; uint8_t v_solverMode_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1735_; 
v_trimProofs_1714_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_1715_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_1716_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_1717_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1718_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_1719_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_1720_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_1721_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_1722_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_1723_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_1724_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_1725_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_config_1627_, 0);
lean_dec(v_unused_1736_);
v___x_1727_ = v_config_1627_;
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_maxSteps_1723_);
lean_dec(v_config_1627_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v_a_1710_);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1710_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_maxSteps_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2, v_trimProofs_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 1, v_binaryProofs_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 2, v_acNf_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 3, v_andFlattening_1717_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 5, v_structures_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 6, v_fixedInt_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 7, v_enums_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 8, v_graphviz_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 9, v_shortCircuit_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*2 + 10, v_solverMode_1725_);
v___x_1730_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1730_);
v___x_1732_ = v___x_1712_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v_config_1627_);
v_a_1738_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1709_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1709_);
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
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1746_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1707_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1707_);
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
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1754_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1705_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1705_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec_ref(v___x_1643_);
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__8));
v___x_1763_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_1762_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1763_) == 0)
{
uint8_t v___x_1764_; 
lean_dec_ref_known(v___x_1763_, 1);
v___x_1764_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1765_; 
lean_dec_ref(v___x_1644_);
v___x_1765_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1793_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1793_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1793_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_timeout_1770_; uint8_t v_trimProofs_1771_; uint8_t v_binaryProofs_1772_; uint8_t v_acNf_1773_; uint8_t v_andFlattening_1774_; uint8_t v_embeddedConstraintSubst_1775_; uint8_t v_fixedInt_1776_; uint8_t v_enums_1777_; uint8_t v_graphviz_1778_; lean_object* v_maxSteps_1779_; uint8_t v_shortCircuit_1780_; uint8_t v_solverMode_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1792_; 
v_timeout_1770_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_1771_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_1772_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_1773_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_1774_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1775_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_fixedInt_1776_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_1777_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_1778_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_1779_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_1780_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_1781_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1783_ = v_config_1627_;
v_isShared_1784_ = v_isSharedCheck_1792_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_maxSteps_1779_);
lean_inc(v_timeout_1770_);
lean_dec(v_config_1627_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1792_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_timeout_1770_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_maxSteps_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*2, v_trimProofs_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*2 + 1, v_binaryProofs_1772_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*2 + 2, v_acNf_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*2 + 3, v_andFlattening_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1775_);
v___x_1786_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
uint8_t v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = lean_unbox(v_a_1766_);
lean_dec(v_a_1766_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*2 + 5, v___x_1787_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*2 + 6, v_fixedInt_1776_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*2 + 7, v_enums_1777_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*2 + 8, v_graphviz_1778_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*2 + 9, v_shortCircuit_1780_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*2 + 10, v_solverMode_1781_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1786_);
v___x_1789_ = v___x_1768_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1786_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v_config_1627_);
v_a_1794_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1765_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1765_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1802_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1763_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1763_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v___x_1643_);
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__9));
v___x_1811_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_1810_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1811_) == 0)
{
uint8_t v___x_1812_; 
lean_dec_ref_known(v___x_1811_, 1);
v___x_1812_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1813_; 
lean_dec_ref(v___x_1644_);
lean_inc_ref(v_item_1628_);
v___x_1813_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_value_1814_; lean_object* v___x_1815_; 
lean_dec_ref_known(v___x_1813_, 1);
v_value_1814_ = lean_ctor_get(v_item_1628_, 2);
lean_inc(v_value_1814_);
lean_dec_ref(v_item_1628_);
v___x_1815_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__1(v_value_1814_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1843_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1843_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1843_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_timeout_1820_; uint8_t v_trimProofs_1821_; uint8_t v_binaryProofs_1822_; uint8_t v_acNf_1823_; uint8_t v_andFlattening_1824_; uint8_t v_embeddedConstraintSubst_1825_; uint8_t v_structures_1826_; uint8_t v_fixedInt_1827_; uint8_t v_enums_1828_; uint8_t v_graphviz_1829_; lean_object* v_maxSteps_1830_; uint8_t v_shortCircuit_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1842_; 
v_timeout_1820_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_1821_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_1822_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_1823_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_1824_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1825_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_1826_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_1827_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_1828_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_1829_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_1830_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_1831_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1833_ = v_config_1627_;
v_isShared_1834_ = v_isSharedCheck_1842_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_maxSteps_1830_);
lean_inc(v_timeout_1820_);
lean_dec(v_config_1627_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1842_;
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
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_timeout_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_maxSteps_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2, v_trimProofs_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 1, v_binaryProofs_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 2, v_acNf_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 3, v_andFlattening_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1825_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 5, v_structures_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 6, v_fixedInt_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 7, v_enums_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 8, v_graphviz_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*2 + 9, v_shortCircuit_1831_);
v___x_1836_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
uint8_t v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = lean_unbox(v_a_1816_);
lean_dec(v_a_1816_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*2 + 10, v___x_1837_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1836_);
v___x_1839_ = v___x_1818_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1836_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_config_1627_);
v_a_1844_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1815_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1815_);
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
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1852_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1813_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1813_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1860_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1811_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1811_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_string_dec_eq(v___x_1643_, v___x_1645_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__10));
v___x_1870_ = lean_string_dec_eq(v___x_1643_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__11));
v___x_1872_ = lean_string_dec_eq(v___x_1643_, v___x_1871_);
lean_dec_ref(v___x_1643_);
if (v___x_1872_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__12));
v___x_1874_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_1873_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1874_) == 0)
{
uint8_t v___x_1875_; 
lean_dec_ref_known(v___x_1874_, 1);
v___x_1875_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_1875_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1876_; 
lean_dec_ref(v___x_1644_);
v___x_1876_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1904_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1904_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1904_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_timeout_1881_; uint8_t v_trimProofs_1882_; uint8_t v_binaryProofs_1883_; uint8_t v_acNf_1884_; uint8_t v_andFlattening_1885_; uint8_t v_embeddedConstraintSubst_1886_; uint8_t v_structures_1887_; uint8_t v_fixedInt_1888_; uint8_t v_enums_1889_; uint8_t v_graphviz_1890_; lean_object* v_maxSteps_1891_; uint8_t v_solverMode_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1903_; 
v_timeout_1881_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_1882_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_1883_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_1884_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_1885_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1886_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_1887_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_1888_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_1889_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_1890_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_1891_ = lean_ctor_get(v_config_1627_, 1);
v_solverMode_1892_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1894_ = v_config_1627_;
v_isShared_1895_ = v_isSharedCheck_1903_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_maxSteps_1891_);
lean_inc(v_timeout_1881_);
lean_dec(v_config_1627_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1903_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_timeout_1881_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_maxSteps_1891_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2, v_trimProofs_1882_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 1, v_binaryProofs_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 2, v_acNf_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 3, v_andFlattening_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 5, v_structures_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 6, v_fixedInt_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 7, v_enums_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*2 + 8, v_graphviz_1890_);
v___x_1897_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
uint8_t v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_unbox(v_a_1877_);
lean_dec(v_a_1877_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*2 + 9, v___x_1898_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*2 + 10, v_solverMode_1892_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1897_);
v___x_1900_ = v___x_1879_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1897_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_config_1627_);
v_a_1905_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1876_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1876_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1913_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1874_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1874_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec_ref(v___x_1643_);
v___x_1921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__13));
v___x_1922_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_1921_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1922_) == 0)
{
uint8_t v___x_1923_; 
lean_dec_ref_known(v___x_1922_, 1);
v___x_1923_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_1923_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1924_; 
lean_dec_ref(v___x_1644_);
lean_inc_ref(v_item_1628_);
v___x_1924_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_value_1925_; lean_object* v___x_1926_; 
lean_dec_ref_known(v___x_1924_, 1);
v_value_1925_ = lean_ctor_get(v_item_1628_, 2);
lean_inc(v_value_1925_);
lean_dec_ref(v_item_1628_);
v___x_1926_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__0(v_value_1925_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1954_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1954_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1954_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_timeout_1931_; uint8_t v_trimProofs_1932_; uint8_t v_binaryProofs_1933_; uint8_t v_acNf_1934_; uint8_t v_andFlattening_1935_; uint8_t v_embeddedConstraintSubst_1936_; uint8_t v_structures_1937_; uint8_t v_fixedInt_1938_; uint8_t v_enums_1939_; uint8_t v_graphviz_1940_; uint8_t v_shortCircuit_1941_; uint8_t v_solverMode_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1952_; 
v_timeout_1931_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_1932_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_1933_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_1934_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_1935_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1936_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_1937_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_1938_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_1939_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_1940_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_shortCircuit_1941_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_1942_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; 
v_unused_1953_ = lean_ctor_get(v_config_1627_, 1);
lean_dec(v_unused_1953_);
v___x_1944_ = v_config_1627_;
v_isShared_1945_ = v_isSharedCheck_1952_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_timeout_1931_);
lean_dec(v_config_1627_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1952_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v_a_1927_);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_timeout_1931_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_a_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2, v_trimProofs_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 1, v_binaryProofs_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 2, v_acNf_1934_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 3, v_andFlattening_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 5, v_structures_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 6, v_fixedInt_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 7, v_enums_1939_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 8, v_graphviz_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 9, v_shortCircuit_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1951_, sizeof(void*)*2 + 10, v_solverMode_1942_);
v___x_1947_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1947_);
v___x_1949_ = v___x_1929_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec_ref(v_config_1627_);
v_a_1955_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1926_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1926_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1963_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1924_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1924_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_1971_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1922_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1922_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v___x_1643_);
v___x_1979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__14));
v___x_1980_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_1979_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1980_) == 0)
{
uint8_t v___x_1981_; 
lean_dec_ref_known(v___x_1980_, 1);
v___x_1981_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_1981_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_1982_; 
lean_dec_ref(v___x_1644_);
v___x_1982_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2010_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2010_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2010_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_timeout_1987_; uint8_t v_trimProofs_1988_; uint8_t v_binaryProofs_1989_; uint8_t v_acNf_1990_; uint8_t v_andFlattening_1991_; uint8_t v_embeddedConstraintSubst_1992_; uint8_t v_structures_1993_; uint8_t v_fixedInt_1994_; uint8_t v_enums_1995_; lean_object* v_maxSteps_1996_; uint8_t v_shortCircuit_1997_; uint8_t v_solverMode_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2009_; 
v_timeout_1987_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_1988_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_1989_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_1990_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_1991_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_1992_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_1993_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_1994_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_1995_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_maxSteps_1996_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_1997_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_1998_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2000_ = v_config_1627_;
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_maxSteps_1996_);
lean_inc(v_timeout_1987_);
lean_dec(v_config_1627_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_timeout_1987_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_maxSteps_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2, v_trimProofs_1988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2 + 1, v_binaryProofs_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2 + 2, v_acNf_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2 + 3, v_andFlattening_1991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2 + 5, v_structures_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2 + 6, v_fixedInt_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2 + 7, v_enums_1995_);
v___x_2003_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
uint8_t v___x_2004_; lean_object* v___x_2006_; 
v___x_2004_ = lean_unbox(v_a_1983_);
lean_dec(v_a_1983_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*2 + 8, v___x_2004_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*2 + 9, v_shortCircuit_1997_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*2 + 10, v_solverMode_1998_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2003_);
v___x_2006_ = v___x_1985_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2003_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v_config_1627_);
v_a_2011_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1982_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1982_);
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
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2019_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1980_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1980_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
else
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__15));
v___x_2028_ = lean_string_dec_lt(v___x_1643_, v___x_2027_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_string_dec_eq(v___x_1643_, v___x_2027_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__16));
v___x_2031_ = lean_string_dec_eq(v___x_1643_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__17));
v___x_2033_ = lean_string_dec_eq(v___x_1643_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__18));
v___x_2035_ = lean_string_dec_eq(v___x_1643_, v___x_2034_);
lean_dec_ref(v___x_1643_);
if (v___x_2035_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__19));
v___x_2037_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_2036_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2037_) == 0)
{
uint8_t v___x_2038_; 
lean_dec_ref_known(v___x_2037_, 1);
v___x_2038_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_2038_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2039_; 
lean_dec_ref(v___x_1644_);
v___x_2039_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2067_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2067_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2067_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_timeout_2044_; uint8_t v_trimProofs_2045_; uint8_t v_binaryProofs_2046_; uint8_t v_acNf_2047_; uint8_t v_andFlattening_2048_; uint8_t v_embeddedConstraintSubst_2049_; uint8_t v_structures_2050_; uint8_t v_enums_2051_; uint8_t v_graphviz_2052_; lean_object* v_maxSteps_2053_; uint8_t v_shortCircuit_2054_; uint8_t v_solverMode_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2066_; 
v_timeout_2044_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_2045_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_2046_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_2047_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_2048_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2049_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_2050_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_enums_2051_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_2052_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_2053_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_2054_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_2055_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2057_ = v_config_1627_;
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_maxSteps_2053_);
lean_inc(v_timeout_2044_);
lean_dec(v_config_1627_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_timeout_2044_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_maxSteps_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*2, v_trimProofs_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*2 + 1, v_binaryProofs_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*2 + 2, v_acNf_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*2 + 3, v_andFlattening_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*2 + 5, v_structures_2050_);
v___x_2060_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
uint8_t v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*2 + 6, v___x_2061_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*2 + 7, v_enums_2051_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*2 + 8, v_graphviz_2052_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*2 + 9, v_shortCircuit_2054_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*2 + 10, v_solverMode_2055_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2060_);
v___x_2063_ = v___x_2042_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2060_);
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
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_config_1627_);
v_a_2068_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2039_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2039_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2076_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2037_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2037_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref(v___x_1643_);
v___x_2084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__20));
v___x_2085_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_2084_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2085_) == 0)
{
uint8_t v___x_2086_; 
lean_dec_ref_known(v___x_2085_, 1);
v___x_2086_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_2086_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref(v___x_1644_);
v___x_2087_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2115_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2115_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2115_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_timeout_2092_; uint8_t v_trimProofs_2093_; uint8_t v_binaryProofs_2094_; uint8_t v_acNf_2095_; uint8_t v_andFlattening_2096_; uint8_t v_embeddedConstraintSubst_2097_; uint8_t v_structures_2098_; uint8_t v_fixedInt_2099_; uint8_t v_graphviz_2100_; lean_object* v_maxSteps_2101_; uint8_t v_shortCircuit_2102_; uint8_t v_solverMode_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2114_; 
v_timeout_2092_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_2093_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_2094_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_2095_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_2096_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2097_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_2098_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_2099_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_graphviz_2100_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_2101_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_2102_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_2103_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2105_ = v_config_1627_;
v_isShared_2106_ = v_isSharedCheck_2114_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_maxSteps_2101_);
lean_inc(v_timeout_2092_);
lean_dec(v_config_1627_);
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
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_timeout_2092_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_maxSteps_2101_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*2, v_trimProofs_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*2 + 1, v_binaryProofs_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*2 + 2, v_acNf_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*2 + 3, v_andFlattening_2096_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*2 + 5, v_structures_2098_);
lean_ctor_set_uint8(v_reuseFailAlloc_2113_, sizeof(void*)*2 + 6, v_fixedInt_2099_);
v___x_2108_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
uint8_t v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_unbox(v_a_2088_);
lean_dec(v_a_2088_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*2 + 7, v___x_2109_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*2 + 8, v_graphviz_2100_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*2 + 9, v_shortCircuit_2102_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*2 + 10, v_solverMode_2103_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2108_);
v___x_2111_ = v___x_2090_;
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
lean_dec_ref(v_config_1627_);
v_a_2116_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2087_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2087_);
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
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2124_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2085_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2085_);
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
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref(v___x_1643_);
v___x_2132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__21));
v___x_2133_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_2132_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2133_) == 0)
{
uint8_t v___x_2134_; 
lean_dec_ref_known(v___x_2133_, 1);
v___x_2134_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_2134_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2135_; 
lean_dec_ref(v___x_1644_);
v___x_2135_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2163_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2163_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2163_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v_timeout_2140_; uint8_t v_trimProofs_2141_; uint8_t v_binaryProofs_2142_; uint8_t v_acNf_2143_; uint8_t v_andFlattening_2144_; uint8_t v_structures_2145_; uint8_t v_fixedInt_2146_; uint8_t v_enums_2147_; uint8_t v_graphviz_2148_; lean_object* v_maxSteps_2149_; uint8_t v_shortCircuit_2150_; uint8_t v_solverMode_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2162_; 
v_timeout_2140_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_2141_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_2142_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_2143_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_2144_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_structures_2145_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_2146_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_2147_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_2148_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_2149_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_2150_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_2151_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2153_ = v_config_1627_;
v_isShared_2154_ = v_isSharedCheck_2162_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_maxSteps_2149_);
lean_inc(v_timeout_2140_);
lean_dec(v_config_1627_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2162_;
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
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_timeout_2140_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_maxSteps_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*2, v_trimProofs_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*2 + 1, v_binaryProofs_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*2 + 2, v_acNf_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2161_, sizeof(void*)*2 + 3, v_andFlattening_2144_);
v___x_2156_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
uint8_t v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_unbox(v_a_2136_);
lean_dec(v_a_2136_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 4, v___x_2157_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 5, v_structures_2145_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 6, v_fixedInt_2146_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 7, v_enums_2147_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 8, v_graphviz_2148_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 9, v_shortCircuit_2150_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*2 + 10, v_solverMode_2151_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2156_);
v___x_2159_ = v___x_2138_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2156_);
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
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_config_1627_);
v_a_2164_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2135_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2135_);
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
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2172_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2133_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2133_);
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
else
{
uint8_t v___x_2180_; 
lean_dec_ref(v___x_1643_);
lean_dec_ref(v_config_1627_);
v___x_2180_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v_item_1628_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v_value_2181_; lean_object* v___x_2182_; 
lean_dec_ref(v___x_1644_);
v_value_2181_ = lean_ctor_get(v_item_1628_, 2);
lean_inc(v_value_2181_);
lean_dec_ref(v_item_1628_);
v___x_2182_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2(v_value_2181_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_2182_;
}
}
}
else
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__22));
v___x_2184_ = lean_string_dec_eq(v___x_1643_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__23));
v___x_2186_ = lean_string_dec_eq(v___x_1643_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__24));
v___x_2188_ = lean_string_dec_eq(v___x_1643_, v___x_2187_);
lean_dec_ref(v___x_1643_);
if (v___x_2188_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__25));
v___x_2190_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_2189_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2190_) == 0)
{
uint8_t v___x_2191_; 
lean_dec_ref_known(v___x_2190_, 1);
v___x_2191_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_2191_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2192_; 
lean_dec_ref(v___x_1644_);
v___x_2192_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2220_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2195_ = v___x_2192_;
v_isShared_2196_ = v_isSharedCheck_2220_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2192_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2220_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_timeout_2197_; uint8_t v_trimProofs_2198_; uint8_t v_acNf_2199_; uint8_t v_andFlattening_2200_; uint8_t v_embeddedConstraintSubst_2201_; uint8_t v_structures_2202_; uint8_t v_fixedInt_2203_; uint8_t v_enums_2204_; uint8_t v_graphviz_2205_; lean_object* v_maxSteps_2206_; uint8_t v_shortCircuit_2207_; uint8_t v_solverMode_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2219_; 
v_timeout_2197_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_2198_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_acNf_2199_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_andFlattening_2200_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2201_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_2202_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_2203_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_2204_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_2205_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_2206_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_2207_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_2208_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2210_ = v_config_1627_;
v_isShared_2211_ = v_isSharedCheck_2219_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_maxSteps_2206_);
lean_inc(v_timeout_2197_);
lean_dec(v_config_1627_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2219_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_timeout_2197_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_maxSteps_2206_);
lean_ctor_set_uint8(v_reuseFailAlloc_2218_, sizeof(void*)*2, v_trimProofs_2198_);
v___x_2213_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
uint8_t v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = lean_unbox(v_a_2193_);
lean_dec(v_a_2193_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 1, v___x_2214_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 2, v_acNf_2199_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 3, v_andFlattening_2200_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2201_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 5, v_structures_2202_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 6, v_fixedInt_2203_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 7, v_enums_2204_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 8, v_graphviz_2205_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 9, v_shortCircuit_2207_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 10, v_solverMode_2208_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2213_);
v___x_2216_ = v___x_2195_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2213_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_config_1627_);
v_a_2221_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2192_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2192_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2229_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2190_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2190_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec_ref(v___x_1643_);
v___x_2237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__26));
v___x_2238_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_2237_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2238_) == 0)
{
uint8_t v___x_2239_; 
lean_dec_ref_known(v___x_2238_, 1);
v___x_2239_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2240_; 
lean_dec_ref(v___x_1644_);
v___x_2240_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2268_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2268_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2268_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_timeout_2245_; uint8_t v_trimProofs_2246_; uint8_t v_binaryProofs_2247_; uint8_t v_acNf_2248_; uint8_t v_embeddedConstraintSubst_2249_; uint8_t v_structures_2250_; uint8_t v_fixedInt_2251_; uint8_t v_enums_2252_; uint8_t v_graphviz_2253_; lean_object* v_maxSteps_2254_; uint8_t v_shortCircuit_2255_; uint8_t v_solverMode_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2267_; 
v_timeout_2245_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_2246_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_2247_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_acNf_2248_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 2);
v_embeddedConstraintSubst_2249_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_2250_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_2251_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_2252_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_2253_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_2254_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_2255_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_2256_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2258_ = v_config_1627_;
v_isShared_2259_ = v_isSharedCheck_2267_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_maxSteps_2254_);
lean_inc(v_timeout_2245_);
lean_dec(v_config_1627_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2267_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_timeout_2245_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_maxSteps_2254_);
lean_ctor_set_uint8(v_reuseFailAlloc_2266_, sizeof(void*)*2, v_trimProofs_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2266_, sizeof(void*)*2 + 1, v_binaryProofs_2247_);
lean_ctor_set_uint8(v_reuseFailAlloc_2266_, sizeof(void*)*2 + 2, v_acNf_2248_);
v___x_2261_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
uint8_t v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_unbox(v_a_2241_);
lean_dec(v_a_2241_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 3, v___x_2262_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2249_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 5, v_structures_2250_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 6, v_fixedInt_2251_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 7, v_enums_2252_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 8, v_graphviz_2253_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 9, v_shortCircuit_2255_);
lean_ctor_set_uint8(v___x_2261_, sizeof(void*)*2 + 10, v_solverMode_2256_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2261_);
v___x_2264_ = v___x_2243_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2261_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v_config_1627_);
v_a_2269_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2240_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2240_);
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
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2277_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2238_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2238_);
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
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec_ref(v___x_1643_);
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__27));
v___x_2286_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1628_, v___x_2285_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2286_) == 0)
{
uint8_t v___x_2287_; 
lean_dec_ref_known(v___x_2286_, 1);
v___x_2287_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1644_);
if (v___x_2287_ == 0)
{
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_item_1637_ = v___x_1644_;
goto v___jp_1636_;
}
else
{
lean_object* v___x_2288_; 
lean_dec_ref(v___x_1644_);
v___x_2288_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2316_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2316_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2316_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_timeout_2293_; uint8_t v_trimProofs_2294_; uint8_t v_binaryProofs_2295_; uint8_t v_andFlattening_2296_; uint8_t v_embeddedConstraintSubst_2297_; uint8_t v_structures_2298_; uint8_t v_fixedInt_2299_; uint8_t v_enums_2300_; uint8_t v_graphviz_2301_; lean_object* v_maxSteps_2302_; uint8_t v_shortCircuit_2303_; uint8_t v_solverMode_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2315_; 
v_timeout_2293_ = lean_ctor_get(v_config_1627_, 0);
v_trimProofs_2294_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2);
v_binaryProofs_2295_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 1);
v_andFlattening_2296_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 3);
v_embeddedConstraintSubst_2297_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 4);
v_structures_2298_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 5);
v_fixedInt_2299_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 6);
v_enums_2300_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 7);
v_graphviz_2301_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 8);
v_maxSteps_2302_ = lean_ctor_get(v_config_1627_, 1);
v_shortCircuit_2303_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 9);
v_solverMode_2304_ = lean_ctor_get_uint8(v_config_1627_, sizeof(void*)*2 + 10);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_config_1627_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2306_ = v_config_1627_;
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_maxSteps_2302_);
lean_inc(v_timeout_2293_);
lean_dec(v_config_1627_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_timeout_2293_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_maxSteps_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*2, v_trimProofs_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*2 + 1, v_binaryProofs_2295_);
v___x_2309_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
uint8_t v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = lean_unbox(v_a_2289_);
lean_dec(v_a_2289_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 2, v___x_2310_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 3, v_andFlattening_2296_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 4, v_embeddedConstraintSubst_2297_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 5, v_structures_2298_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 6, v_fixedInt_2299_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 7, v_enums_2300_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 8, v_graphviz_2301_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 9, v_shortCircuit_2303_);
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 10, v_solverMode_2304_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2309_);
v___x_2312_ = v___x_2291_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2309_);
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
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v_config_1627_);
v_a_2317_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2288_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2288_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2325_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2286_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2286_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
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
}
}
else
{
lean_dec_ref(v_config_1627_);
v_item_1637_ = v_item_1628_;
goto v___jp_1636_;
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v_item_1628_);
lean_dec_ref(v_config_1627_);
v_a_2333_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_1641_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_1641_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
v___jp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___closed__0));
v___x_1639_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1637_, v___x_1638_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_2341_, lean_object* v_item_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___lam__0(v_config_2341_, v_item_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(lean_object* v_e_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___redArg(v_e_2353_, v___y_2357_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4___boxed(lean_object* v_e_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__4(v_e_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(lean_object* v_00_u03b1_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___redArg();
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__6(v_00_u03b1_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(lean_object* v_00_u03b1_2389_, lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___redArg(v_msg_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2399_, lean_object* v_msg_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5(v_00_u03b1_2399_, v_msg_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(lean_object* v_msgData_2409_, lean_object* v_macroStack_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___redArg(v_msgData_2409_, v_macroStack_2410_, v___y_2415_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6___boxed(lean_object* v_msgData_2419_, lean_object* v_macroStack_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2_spec__5_spec__6(v_msgData_2419_, v_macroStack_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2428_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = lean_box(0);
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_instEvalExprBVDecideConfig_evalExpr___closed__2));
v___x_2431_ = l_Lean_mkConst(v___x_2430_, v___x_2429_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__0);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(lean_object* v_cfg_2434_, lean_object* v_cfgItem_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___closed__1);
v___x_2444_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_2434_, v_cfgItem_2435_, v___x_2443_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0___boxed(lean_object* v_cfg_2445_, lean_object* v_cfgItem_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___lam__0(v_cfg_2445_, v_cfgItem_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v_cfgItem_2446_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object* v_cfg_2456_, lean_object* v_init_2457_, uint8_t v_logExceptions_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_onErr_2463_; lean_object* v_eval_2464_; 
v_onErr_2463_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___closed__0));
v_eval_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem___closed__0));
if (v_logExceptions_2458_ == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2464_, v_init_2457_, v_cfg_2456_, v_onErr_2463_, v_logExceptions_2458_, v_a_2460_, v_a_2461_);
return v___x_2465_;
}
else
{
uint8_t v_recover_2466_; lean_object* v___x_2467_; 
v_recover_2466_ = lean_ctor_get_uint8(v_a_2459_, sizeof(void*)*1);
v___x_2467_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_2464_, v_init_2457_, v_cfg_2456_, v_onErr_2463_, v_recover_2466_, v_a_2460_, v_a_2461_);
return v___x_2467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_2468_, lean_object* v_init_2469_, lean_object* v_logExceptions_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
uint8_t v_logExceptions_boxed_2475_; lean_object* v_res_2476_; 
v_logExceptions_boxed_2475_ = lean_unbox(v_logExceptions_2470_);
v_res_2476_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2468_, v_init_2469_, v_logExceptions_boxed_2475_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec_ref(v_a_2471_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(lean_object* v_cfg_2477_, lean_object* v_init_2478_, uint8_t v_logExceptions_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_2477_, v_init_2478_, v_logExceptions_2479_, v_a_2480_, v_a_2486_, v_a_2487_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___boxed(lean_object* v_cfg_2490_, lean_object* v_init_2491_, lean_object* v_logExceptions_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
uint8_t v_logExceptions_boxed_2502_; lean_object* v_res_2503_; 
v_logExceptions_boxed_2502_ = lean_unbox(v_logExceptions_2492_);
v_res_2503_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig(v_cfg_2490_, v_init_2491_, v_logExceptions_boxed_2502_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
return v_res_2503_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__0);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2508_ = lean_unsigned_to_nat(0u);
v___x_2509_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
lean_ctor_set(v___x_2509_, 2, v___x_2508_);
lean_ctor_set(v___x_2509_, 3, v___x_2508_);
lean_ctor_set(v___x_2509_, 4, v___x_2507_);
lean_ctor_set(v___x_2509_, 5, v___x_2507_);
lean_ctor_set(v___x_2509_, 6, v___x_2507_);
lean_ctor_set(v___x_2509_, 7, v___x_2507_);
lean_ctor_set(v___x_2509_, 8, v___x_2507_);
lean_ctor_set(v___x_2509_, 9, v___x_2507_);
lean_ctor_set(v___x_2509_, 10, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_unsigned_to_nat(32u);
v___x_2511_ = lean_mk_empty_array_with_capacity(v___x_2510_);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2513_ = ((size_t)5ULL);
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = lean_unsigned_to_nat(32u);
v___x_2516_ = lean_mk_empty_array_with_capacity(v___x_2515_);
v___x_2517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__3);
v___x_2518_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v___x_2516_);
lean_ctor_set(v___x_2518_, 2, v___x_2514_);
lean_ctor_set(v___x_2518_, 3, v___x_2514_);
lean_ctor_set_usize(v___x_2518_, 4, v___x_2513_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2519_ = lean_box(1);
v___x_2520_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__4);
v___x_2521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__1);
v___x_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2520_);
lean_ctor_set(v___x_2522_, 2, v___x_2519_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__6));
v___x_2525_ = l_Lean_stringToMessageData(v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__8));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__10));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__12));
v___x_2534_ = l_Lean_stringToMessageData(v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__14));
v___x_2537_ = l_Lean_stringToMessageData(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__16));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__18));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_msg_2544_, lean_object* v_declHint_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v_env_2550_; uint8_t v___x_2551_; 
v___x_2548_ = lean_box(0);
v___x_2549_ = lean_st_ref_get(v___y_2546_);
v_env_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc_ref(v_env_2550_);
lean_dec(v___x_2549_);
v___x_2551_ = l_Lean_Name_isAnonymous(v_declHint_2545_);
if (v___x_2551_ == 0)
{
uint8_t v_isExporting_2552_; 
v_isExporting_2552_ = lean_ctor_get_uint8(v_env_2550_, sizeof(void*)*8);
if (v_isExporting_2552_ == 0)
{
lean_object* v___x_2553_; 
lean_dec_ref(v_env_2550_);
lean_dec(v_declHint_2545_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_msg_2544_);
return v___x_2553_;
}
else
{
lean_object* v___x_2554_; uint8_t v___x_2555_; 
lean_inc_ref(v_env_2550_);
v___x_2554_ = l_Lean_Environment_setExporting(v_env_2550_, v___x_2551_);
lean_inc(v_declHint_2545_);
lean_inc_ref(v___x_2554_);
v___x_2555_ = l_Lean_Environment_contains(v___x_2554_, v_declHint_2545_, v_isExporting_2552_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
lean_dec_ref(v___x_2554_);
lean_dec_ref(v_env_2550_);
lean_dec(v_declHint_2545_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_msg_2544_);
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v_c_2562_; lean_object* v___x_2563_; 
v___x_2557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
v___x_2559_ = l_Lean_Options_empty;
v___x_2560_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2554_);
lean_ctor_set(v___x_2560_, 1, v___x_2557_);
lean_ctor_set(v___x_2560_, 2, v___x_2558_);
lean_ctor_set(v___x_2560_, 3, v___x_2559_);
lean_inc(v_declHint_2545_);
v___x_2561_ = l_Lean_MessageData_ofConstName(v_declHint_2545_, v___x_2551_);
v_c_2562_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2562_, 0, v___x_2560_);
lean_ctor_set(v_c_2562_, 1, v___x_2561_);
v___x_2563_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2550_, v_declHint_2545_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec_ref(v_env_2550_);
lean_dec(v_declHint_2545_);
v___x_2564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v_c_2562_);
v___x_2566_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__9);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_MessageData_note(v___x_2567_);
v___x_2569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_msg_2544_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
else
{
lean_object* v_val_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2605_; 
v_val_2571_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2573_ = v___x_2563_;
v_isShared_2574_ = v_isSharedCheck_2605_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_val_2571_);
lean_dec(v___x_2563_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2605_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v_mod_2577_; uint8_t v___x_2578_; 
v___x_2575_ = l_Lean_Environment_header(v_env_2550_);
lean_dec_ref(v_env_2550_);
v___x_2576_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2575_);
v_mod_2577_ = lean_array_get(v___x_2548_, v___x_2576_, v_val_2571_);
lean_dec(v_val_2571_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = l_Lean_isPrivateName(v_declHint_2545_);
lean_dec(v_declHint_2545_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__11);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v_c_2562_);
v___x_2581_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__13);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_MessageData_ofName(v_mod_2577_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__15);
v___x_2586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = l_Lean_MessageData_note(v___x_2586_);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_msg_2544_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2588_);
v___x_2590_ = v___x_2573_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__7);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v_c_2562_);
v___x_2594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__17);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = l_Lean_MessageData_ofName(v_mod_2577_);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__19);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = l_Lean_MessageData_note(v___x_2599_);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v_msg_2544_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2601_);
v___x_2603_ = v___x_2573_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2606_; 
lean_dec_ref(v_env_2550_);
lean_dec(v_declHint_2545_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_msg_2544_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_msg_2607_, lean_object* v_declHint_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2607_, v_declHint_2608_, v___y_2609_);
lean_dec(v___y_2609_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_msg_2612_, lean_object* v_declHint_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2627_; 
v___x_2617_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2612_, v_declHint_2613_, v___y_2615_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2627_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2627_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = l_Lean_unknownIdentifierMessageTag;
v___x_2623_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v_a_2618_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2623_);
v___x_2625_ = v___x_2620_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_msg_2628_, lean_object* v_declHint_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2628_, v_declHint_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(lean_object* v_msgData_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; lean_object* v_toCold_2639_; lean_object* v_env_2640_; lean_object* v_options_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2638_ = lean_st_ref_get(v___y_2636_);
v_toCold_2639_ = lean_ctor_get(v___y_2635_, 0);
v_env_2640_ = lean_ctor_get(v___x_2638_, 0);
lean_inc_ref(v_env_2640_);
lean_dec(v___x_2638_);
v_options_2641_ = lean_ctor_get(v_toCold_2639_, 2);
v___x_2642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__2);
v___x_2643_ = lean_unsigned_to_nat(32u);
v___x_2644_ = lean_mk_empty_array_with_capacity(v___x_2643_);
lean_dec_ref(v___x_2644_);
v___x_2645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___closed__5);
lean_inc_ref(v_options_2641_);
v___x_2646_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2646_, 0, v_env_2640_);
lean_ctor_set(v___x_2646_, 1, v___x_2642_);
lean_ctor_set(v___x_2646_, 2, v___x_2645_);
lean_ctor_set(v___x_2646_, 3, v_options_2641_);
v___x_2647_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
lean_ctor_set(v___x_2647_, 1, v_msgData_2634_);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9___boxed(lean_object* v_msgData_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msgData_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_msg_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_ref_2658_; lean_object* v___x_2659_; lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2668_; 
v_ref_2658_ = lean_ctor_get(v___y_2655_, 2);
v___x_2659_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8_spec__9(v_msg_2654_, v___y_2655_, v___y_2656_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2668_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2668_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2666_; 
lean_inc(v_ref_2658_);
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_ref_2658_);
lean_ctor_set(v___x_2664_, 1, v_a_2660_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set_tag(v___x_2662_, 1);
lean_ctor_set(v___x_2662_, 0, v___x_2664_);
v___x_2666_ = v___x_2662_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_msg_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_ref_2674_, lean_object* v_msg_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_toCold_2679_; lean_object* v_currRecDepth_2680_; lean_object* v_ref_2681_; uint8_t v_diag_2682_; uint8_t v_suppressElabErrors_2683_; lean_object* v_ref_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_toCold_2679_ = lean_ctor_get(v___y_2676_, 0);
v_currRecDepth_2680_ = lean_ctor_get(v___y_2676_, 1);
v_ref_2681_ = lean_ctor_get(v___y_2676_, 2);
v_diag_2682_ = lean_ctor_get_uint8(v___y_2676_, sizeof(void*)*3);
v_suppressElabErrors_2683_ = lean_ctor_get_uint8(v___y_2676_, sizeof(void*)*3 + 1);
v_ref_2684_ = l_Lean_replaceRef(v_ref_2674_, v_ref_2681_);
lean_inc(v_currRecDepth_2680_);
lean_inc_ref(v_toCold_2679_);
v___x_2685_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2685_, 0, v_toCold_2679_);
lean_ctor_set(v___x_2685_, 1, v_currRecDepth_2680_);
lean_ctor_set(v___x_2685_, 2, v_ref_2684_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*3, v_diag_2682_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*3 + 1, v_suppressElabErrors_2683_);
v___x_2686_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_2675_, v___x_2685_, v___y_2677_);
lean_dec_ref_known(v___x_2685_, 3);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_ref_2687_, lean_object* v_msg_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2687_, v_msg_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v_ref_2687_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2693_, lean_object* v_msg_2694_, lean_object* v_declHint_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v_a_2700_; lean_object* v___x_2701_; 
v___x_2699_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5(v_msg_2694_, v_declHint_2695_, v___y_2696_, v___y_2697_);
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
v___x_2701_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_2693_, v_a_2700_, v___y_2696_, v___y_2697_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2702_, lean_object* v_msg_2703_, lean_object* v_declHint_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2702_, v_msg_2703_, v_declHint_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v_ref_2702_);
return v_res_2708_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2711_ = l_Lean_stringToMessageData(v___x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2712_, lean_object* v_constName_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2717_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2718_ = 0;
lean_inc(v_constName_2713_);
v___x_2719_ = l_Lean_MessageData_ofConstName(v_constName_2713_, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2717_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2712_, v___x_2722_, v_constName_2713_, v___y_2714_, v___y_2715_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2724_, lean_object* v_constName_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_2724_, v_constName_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_ref_2724_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(lean_object* v_constName_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_ref_2734_; lean_object* v___x_2735_; 
v_ref_2734_ = lean_ctor_get(v___y_2731_, 2);
v___x_2735_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_2734_, v_constName_2730_, v___y_2731_, v___y_2732_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(lean_object* v_constName_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v_env_2746_; uint8_t v___x_2747_; lean_object* v___x_2748_; 
v___x_2745_ = lean_st_ref_get(v___y_2743_);
v_env_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc_ref(v_env_2746_);
lean_dec(v___x_2745_);
v___x_2747_ = 0;
lean_inc(v_constName_2741_);
v___x_2748_ = l_Lean_Environment_find_x3f(v_env_2746_, v_constName_2741_, v___x_2747_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_2741_, v___y_2742_, v___y_2743_);
return v___x_2749_;
}
else
{
lean_object* v_val_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_constName_2741_);
v_val_2750_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2748_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_val_2750_);
lean_dec(v___x_2748_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set_tag(v___x_2752_, 0);
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_val_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0___boxed(lean_object* v_constName_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_constName_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(uint8_t v___x_2763_, lean_object* v_x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
if (lean_obj_tag(v_x_2764_) == 0)
{
uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = 1;
v___x_2769_ = lean_box(v___x_2768_);
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
return v___x_2770_;
}
else
{
lean_object* v_head_2771_; lean_object* v_tail_2772_; lean_object* v___y_2774_; uint8_t v_a_2775_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_head_2771_ = lean_ctor_get(v_x_2764_, 0);
lean_inc(v_head_2771_);
v_tail_2772_ = lean_ctor_get(v_x_2764_, 1);
lean_inc(v_tail_2772_);
lean_dec_ref_known(v_x_2764_, 2);
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_head_2771_, v___y_2765_, v___y_2766_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2794_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2794_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2794_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
if (lean_obj_tag(v_a_2779_) == 6)
{
lean_object* v_val_2783_; lean_object* v_numFields_2784_; uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v_val_2783_ = lean_ctor_get(v_a_2779_, 0);
lean_inc_ref(v_val_2783_);
lean_dec_ref_known(v_a_2779_, 1);
v_numFields_2784_ = lean_ctor_get(v_val_2783_, 4);
lean_inc(v_numFields_2784_);
lean_dec_ref(v_val_2783_);
v___x_2785_ = lean_nat_dec_eq(v_numFields_2784_, v___x_2777_);
lean_dec(v_numFields_2784_);
v___x_2786_ = lean_box(v___x_2785_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2786_);
v___x_2788_ = v___x_2781_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v___y_2774_ = v___x_2788_;
v_a_2775_ = v___x_2785_;
goto v___jp_2773_;
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
lean_dec(v_a_2779_);
v___x_2790_ = lean_box(v___x_2763_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2790_);
v___x_2792_ = v___x_2781_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
v___y_2774_ = v___x_2792_;
v_a_2775_ = v___x_2763_;
goto v___jp_2773_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_tail_2772_);
v_a_2795_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2778_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2778_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
v___jp_2773_:
{
if (v_a_2775_ == 0)
{
lean_dec(v_tail_2772_);
return v___y_2774_;
}
else
{
lean_dec_ref(v___y_2774_);
v_x_2764_ = v_tail_2772_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2___boxed(lean_object* v___x_2803_, lean_object* v_x_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v___x_4218__boxed_2808_; lean_object* v_res_2809_; 
v___x_4218__boxed_2808_ = lean_unbox(v___x_2803_);
v_res_2809_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v___x_4218__boxed_2808_, v_x_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(lean_object* v_declName_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_2810_, v___y_2811_, v___y_2812_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2870_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2870_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2870_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
if (lean_obj_tag(v_a_2815_) == 5)
{
lean_object* v_val_2819_; lean_object* v_toConstantVal_2820_; lean_object* v_numParams_2821_; lean_object* v_numIndices_2822_; lean_object* v_ctors_2823_; uint8_t v_isRec_2824_; uint8_t v_isUnsafe_2825_; lean_object* v_type_2826_; uint8_t v___x_2827_; 
v_val_2819_ = lean_ctor_get(v_a_2815_, 0);
lean_inc_ref(v_val_2819_);
lean_dec_ref_known(v_a_2815_, 1);
v_toConstantVal_2820_ = lean_ctor_get(v_val_2819_, 0);
v_numParams_2821_ = lean_ctor_get(v_val_2819_, 1);
lean_inc(v_numParams_2821_);
v_numIndices_2822_ = lean_ctor_get(v_val_2819_, 2);
lean_inc(v_numIndices_2822_);
v_ctors_2823_ = lean_ctor_get(v_val_2819_, 4);
lean_inc(v_ctors_2823_);
v_isRec_2824_ = lean_ctor_get_uint8(v_val_2819_, sizeof(void*)*6);
v_isUnsafe_2825_ = lean_ctor_get_uint8(v_val_2819_, sizeof(void*)*6 + 1);
v_type_2826_ = lean_ctor_get(v_toConstantVal_2820_, 2);
v___x_2827_ = l_Lean_Expr_isProp(v_type_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2828_ = l_Lean_InductiveVal_numTypeFormers(v_val_2819_);
lean_dec_ref(v_val_2819_);
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = lean_nat_dec_eq(v___x_2828_, v___x_2829_);
lean_dec(v___x_2828_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2833_; 
lean_dec(v_ctors_2823_);
lean_dec(v_numIndices_2822_);
lean_dec(v_numParams_2821_);
v___x_2831_ = lean_box(v___x_2830_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2831_);
v___x_2833_ = v___x_2817_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
else
{
lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = lean_nat_dec_eq(v_numIndices_2822_, v___x_2835_);
lean_dec(v_numIndices_2822_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
lean_dec(v_ctors_2823_);
lean_dec(v_numParams_2821_);
v___x_2837_ = lean_box(v___x_2836_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2837_);
v___x_2839_ = v___x_2817_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
else
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_nat_dec_eq(v_numParams_2821_, v___x_2835_);
lean_dec(v_numParams_2821_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
lean_dec(v_ctors_2823_);
v___x_2842_ = lean_box(v___x_2841_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2842_);
v___x_2844_ = v___x_2817_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
else
{
uint8_t v___x_2846_; 
v___x_2846_ = l_List_isEmpty___redArg(v_ctors_2823_);
if (v___x_2846_ == 0)
{
if (v_isRec_2824_ == 0)
{
if (v_isUnsafe_2825_ == 0)
{
lean_object* v___x_2847_; 
lean_del_object(v___x_2817_);
v___x_2847_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1_spec__2(v_isUnsafe_2825_, v_ctors_2823_, v___y_2811_, v___y_2812_);
return v___x_2847_;
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_dec(v_ctors_2823_);
v___x_2848_ = lean_box(v_isRec_2824_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2848_);
v___x_2850_ = v___x_2817_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
lean_dec(v_ctors_2823_);
v___x_2852_ = lean_box(v___x_2846_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2852_);
v___x_2854_ = v___x_2817_;
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
else
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_dec(v_ctors_2823_);
v___x_2856_ = lean_box(v___x_2827_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2856_);
v___x_2858_ = v___x_2817_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
else
{
uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
lean_dec(v_ctors_2823_);
lean_dec(v_numIndices_2822_);
lean_dec(v_numParams_2821_);
lean_dec_ref(v_val_2819_);
v___x_2860_ = 0;
v___x_2861_ = lean_box(v___x_2860_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2861_);
v___x_2863_ = v___x_2817_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_dec(v_a_2815_);
v___x_2865_ = 0;
v___x_2866_ = lean_box(v___x_2865_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2866_);
v___x_2868_ = v___x_2817_;
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
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
v_a_2871_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2814_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2814_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1___boxed(lean_object* v_declName_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(lean_object* v_cfg_2884_, lean_object* v_declName_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
uint8_t v_structures_2889_; uint8_t v_enums_2890_; uint8_t v_a_2892_; 
v_structures_2889_ = lean_ctor_get_uint8(v_cfg_2884_, sizeof(void*)*2 + 5);
v_enums_2890_ = lean_ctor_get_uint8(v_cfg_2884_, sizeof(void*)*2 + 7);
if (v_enums_2890_ == 0)
{
v_a_2892_ = v_enums_2890_;
goto v___jp_2891_;
}
else
{
lean_object* v___x_2930_; 
lean_inc(v_declName_2885_);
v___x_2930_ = l_Lean_isEnumType___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__1(v_declName_2885_, v_a_2886_, v_a_2887_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2941_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2941_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2941_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_unbox(v_a_2931_);
if (v___x_2935_ == 0)
{
uint8_t v___x_2936_; 
lean_del_object(v___x_2933_);
v___x_2936_ = lean_unbox(v_a_2931_);
lean_dec(v_a_2931_);
v_a_2892_ = v___x_2936_;
goto v___jp_2891_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
lean_dec(v_a_2931_);
lean_dec(v_declName_2885_);
v___x_2937_ = lean_box(v_enums_2890_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2937_);
v___x_2939_ = v___x_2933_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_dec(v_declName_2885_);
return v___x_2930_;
}
}
v___jp_2891_:
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_st_ref_get(v_a_2887_);
if (v_structures_2889_ == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
lean_dec(v___x_2893_);
lean_dec(v_declName_2885_);
v___x_2894_ = lean_box(v_a_2892_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
else
{
if (v_a_2892_ == 0)
{
lean_object* v_env_2896_; uint8_t v___x_2897_; 
v_env_2896_ = lean_ctor_get(v___x_2893_, 0);
lean_inc_ref(v_env_2896_);
lean_dec(v___x_2893_);
lean_inc(v_declName_2885_);
v___x_2897_ = l_Lean_isStructure(v_env_2896_, v_declName_2885_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec(v_declName_2885_);
v___x_2898_ = lean_box(v_a_2892_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0(v_declName_2885_, v_a_2886_, v_a_2887_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2919_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2919_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2919_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
if (lean_obj_tag(v_a_2901_) == 5)
{
lean_object* v_val_2905_; uint8_t v_isRec_2906_; 
v_val_2905_ = lean_ctor_get(v_a_2901_, 0);
lean_inc_ref(v_val_2905_);
lean_dec_ref_known(v_a_2901_, 1);
v_isRec_2906_ = lean_ctor_get_uint8(v_val_2905_, sizeof(void*)*6);
lean_dec_ref(v_val_2905_);
if (v_isRec_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = lean_box(v___x_2897_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2907_);
v___x_2909_ = v___x_2903_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2911_ = lean_box(v_a_2892_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2911_);
v___x_2913_ = v___x_2903_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
else
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
lean_dec(v_a_2901_);
v___x_2915_ = lean_box(v_a_2892_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2915_);
v___x_2917_ = v___x_2903_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
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
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v_a_2920_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2900_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2900_);
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
lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec(v___x_2893_);
lean_dec(v_declName_2885_);
v___x_2928_ = lean_box(v_a_2892_);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType___boxed(lean_object* v_cfg_2942_, lean_object* v_declName_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_2942_, v_declName_2943_, v_a_2944_, v_a_2945_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec_ref(v_cfg_2942_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(lean_object* v_00_u03b1_2948_, lean_object* v_constName_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___redArg(v_constName_2949_, v___y_2950_, v___y_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_constName_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0(v_00_u03b1_2954_, v_constName_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2960_, lean_object* v_ref_2961_, lean_object* v_constName_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___redArg(v_ref_2961_, v_constName_2962_, v___y_2963_, v___y_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2967_, lean_object* v_ref_2968_, lean_object* v_constName_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1(v_00_u03b1_2967_, v_ref_2968_, v_constName_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v_ref_2968_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2974_, lean_object* v_ref_2975_, lean_object* v_msg_2976_, lean_object* v_declHint_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2975_, v_msg_2976_, v_declHint_2977_, v___y_2978_, v___y_2979_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2982_, lean_object* v_ref_2983_, lean_object* v_msg_2984_, lean_object* v_declHint_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2982_, v_ref_2983_, v_msg_2984_, v_declHint_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v_ref_2983_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_2990_, lean_object* v_declHint_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_msg_2990_, v_declHint_2991_, v___y_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_2996_, lean_object* v_declHint_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_2996_, v_declHint_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b1_3002_, lean_object* v_ref_3003_, lean_object* v_msg_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_ref_3003_, v_msg_3004_, v___y_3005_, v___y_3006_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b1_3009_, lean_object* v_ref_3010_, lean_object* v_msg_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6(v_00_u03b1_3009_, v_ref_3010_, v_msg_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v_ref_3010_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b1_3016_, lean_object* v_msg_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_msg_3017_, v___y_3018_, v___y_3019_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3022_, lean_object* v_msg_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8(v_00_u03b1_3022_, v_msg_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(lean_object* v_a_3028_, lean_object* v_as_3029_, size_t v_i_3030_, size_t v_stop_3031_){
_start:
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_usize_dec_eq(v_i_3030_, v_stop_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = lean_array_uget_borrowed(v_as_3029_, v_i_3030_);
v___x_3034_ = lean_name_eq(v_a_3028_, v___x_3033_);
if (v___x_3034_ == 0)
{
size_t v___x_3035_; size_t v___x_3036_; 
v___x_3035_ = ((size_t)1ULL);
v___x_3036_ = lean_usize_add(v_i_3030_, v___x_3035_);
v_i_3030_ = v___x_3036_;
goto _start;
}
else
{
return v___x_3034_;
}
}
else
{
uint8_t v___x_3038_; 
v___x_3038_ = 0;
return v___x_3038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0___boxed(lean_object* v_a_3039_, lean_object* v_as_3040_, lean_object* v_i_3041_, lean_object* v_stop_3042_){
_start:
{
size_t v_i_boxed_3043_; size_t v_stop_boxed_3044_; uint8_t v_res_3045_; lean_object* v_r_3046_; 
v_i_boxed_3043_ = lean_unbox_usize(v_i_3041_);
lean_dec(v_i_3041_);
v_stop_boxed_3044_ = lean_unbox_usize(v_stop_3042_);
lean_dec(v_stop_3042_);
v_res_3045_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3039_, v_as_3040_, v_i_boxed_3043_, v_stop_boxed_3044_);
lean_dec_ref(v_as_3040_);
lean_dec(v_a_3039_);
v_r_3046_ = lean_box(v_res_3045_);
return v_r_3046_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(lean_object* v_as_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_array_get_size(v_as_3047_);
v___x_3051_ = lean_nat_dec_lt(v___x_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
return v___x_3051_;
}
else
{
if (v___x_3051_ == 0)
{
return v___x_3051_;
}
else
{
size_t v___x_3052_; size_t v___x_3053_; uint8_t v___x_3054_; 
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = lean_usize_of_nat(v___x_3050_);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0_spec__0(v_a_3048_, v_as_3047_, v___x_3052_, v___x_3053_);
return v___x_3054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0___boxed(lean_object* v_as_3055_, lean_object* v_a_3056_){
_start:
{
uint8_t v_res_3057_; lean_object* v_r_3058_; 
v_res_3057_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_as_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec_ref(v_as_3055_);
v_r_3058_ = lean_box(v_res_3057_);
return v_r_3058_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__0));
v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(lean_object* v_cfg_3062_, lean_object* v_as_3063_, size_t v_sz_3064_, size_t v_i_3065_, lean_object* v_b_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_a_3071_; uint8_t v___x_3075_; 
v___x_3075_ = lean_usize_dec_lt(v_i_3065_, v_sz_3064_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_b_3066_);
return v___x_3076_;
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3077_ = lean_array_uget_borrowed(v_as_3063_, v_i_3065_);
v___x_3078_ = lean_box(0);
lean_inc(v_a_3077_);
v___x_3079_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_3077_, v___x_3078_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3084_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc_n(v_a_3080_, 2);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3084_ = l_Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType(v_cfg_3062_, v_a_3080_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; uint8_t v___x_3086_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3084_, 1);
v___x_3086_ = lean_unbox(v_a_3085_);
lean_dec(v_a_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3087_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_elabBVDecideConfig_evalConfigItem_spec__2___closed__5);
lean_inc(v_a_3080_);
v___x_3088_ = l_Lean_MessageData_ofName(v_a_3080_);
v___x_3089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3087_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___closed__1);
v___x_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_a_3077_, v___x_3091_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_dec_ref_known(v___x_3092_, 1);
goto v___jp_3081_;
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_a_3080_);
lean_dec_ref(v_b_3066_);
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
goto v___jp_3081_;
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec(v_a_3080_);
lean_dec_ref(v_b_3066_);
v_a_3101_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3084_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3084_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
v___jp_3081_:
{
uint8_t v___x_3082_; 
v___x_3082_ = l_Array_contains___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__0(v_b_3066_, v_a_3080_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_array_push(v_b_3066_, v_a_3080_);
v_a_3071_ = v___x_3083_;
goto v___jp_3070_;
}
else
{
lean_dec(v_a_3080_);
v_a_3071_ = v_b_3066_;
goto v___jp_3070_;
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v_b_3066_);
v_a_3109_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3079_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3079_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
v___jp_3070_:
{
size_t v___x_3072_; size_t v___x_3073_; 
v___x_3072_ = ((size_t)1ULL);
v___x_3073_ = lean_usize_add(v_i_3065_, v___x_3072_);
v_i_3065_ = v___x_3073_;
v_b_3066_ = v_a_3071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1___boxed(lean_object* v_cfg_3117_, lean_object* v_as_3118_, lean_object* v_sz_3119_, lean_object* v_i_3120_, lean_object* v_b_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
size_t v_sz_boxed_3125_; size_t v_i_boxed_3126_; lean_object* v_res_3127_; 
v_sz_boxed_3125_ = lean_unbox_usize(v_sz_3119_);
lean_dec(v_sz_3119_);
v_i_boxed_3126_ = lean_unbox_usize(v_i_3120_);
lean_dec(v_i_3120_);
v_res_3127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3117_, v_as_3118_, v_sz_boxed_3125_, v_i_boxed_3126_, v_b_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v_as_3118_);
lean_dec_ref(v_cfg_3117_);
return v_res_3127_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__3));
v___x_3137_ = l_Lean_stringToMessageData(v___x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object* v_stx_3140_, lean_object* v_cfg_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
if (lean_obj_tag(v_stx_3140_) == 1)
{
lean_object* v_val_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3180_; 
v_val_3145_ = lean_ctor_get(v_stx_3140_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_stx_3140_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3147_ = v_stx_3140_;
v_isShared_3148_ = v_isSharedCheck_3180_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_val_3145_);
lean_dec(v_stx_3140_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3180_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__2));
lean_inc(v_val_3145_);
v___x_3150_ = l_Lean_Syntax_isOfKind(v_val_3145_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_del_object(v___x_3147_);
v___x_3151_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4, &l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__4);
v___x_3152_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_val_3145_, v___x_3151_, v_a_3142_, v_a_3143_);
lean_dec(v_val_3145_);
return v___x_3152_;
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v_ids_3155_; lean_object* v_types_3156_; lean_object* v___x_3157_; size_t v_sz_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v___x_3153_ = lean_unsigned_to_nat(2u);
v___x_3154_ = l_Lean_Syntax_getArg(v_val_3145_, v___x_3153_);
lean_dec(v_val_3145_);
v_ids_3155_ = l_Lean_Syntax_getArgs(v___x_3154_);
lean_dec(v___x_3154_);
v_types_3156_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___closed__5));
v___x_3157_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_ids_3155_);
lean_dec_ref(v_ids_3155_);
v_sz_3158_ = lean_array_size(v___x_3157_);
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_elabBVDecideTypes_spec__1(v_cfg_3141_, v___x_3157_, v_sz_3158_, v___x_3159_, v_types_3156_, v_a_3142_, v_a_3143_);
lean_dec_ref(v___x_3157_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3171_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3171_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3171_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3161_);
v___x_3166_ = v___x_3147_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3168_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3166_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
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
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_del_object(v___x_3147_);
v_a_3172_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3160_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3160_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v_stx_3140_);
v___x_3181_ = lean_box(0);
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes___boxed(lean_object* v_stx_3183_, lean_object* v_cfg_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_stx_3183_, v_cfg_3184_, v_a_3185_, v_a_3186_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec_ref(v_cfg_3184_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__4_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_));
v___x_3204_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3201_, v___x_3202_, v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2____boxed(lean_object* v_a_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_1523930783____hygCtx___hyg_2_();
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3224_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_));
v___x_3227_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_3224_, v___x_3225_, v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2____boxed(lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_980589113____hygCtx___hyg_2_();
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3239_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_));
v___x_3242_ = l_Lean_Meta_registerSimpAttr(v___x_3239_, v___x_3240_, v___x_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2____boxed(lean_object* v_a_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_2280756816____hygCtx___hyg_2_();
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(lean_object* v_e_3245_){
_start:
{
if (lean_obj_tag(v_e_3245_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3255_; 
v_a_3247_ = lean_ctor_get(v_e_3245_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v_e_3245_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3249_ = v_e_3245_;
v_isShared_3250_ = v_isSharedCheck_3255_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v_e_3245_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3255_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3251_ = lean_mk_io_user_error(v_a_3247_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 1);
lean_ctor_set(v___x_3249_, 0, v___x_3251_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
v_a_3256_ = lean_ctor_get(v_e_3245_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_e_3245_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v_e_3245_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v_e_3245_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
lean_ctor_set_tag(v___x_3258_, 0);
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_e_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3264_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_3267_, lean_object* v_e_3268_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v_e_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_3271_, lean_object* v_e_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0(v_00_u03b1_3271_, v_e_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v_declName_3275_, lean_object* v_stx_3276_, uint8_t v_attrKind_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; lean_object* v_env_3282_; lean_object* v_ref_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3281_ = lean_st_ref_get(v___y_3279_);
v_env_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc_ref_n(v_env_3282_, 2);
lean_dec(v___x_3281_);
v_ref_3283_ = lean_ctor_get(v___y_3278_, 2);
v___x_3284_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_metaIntToBitVecName));
v___x_3285_ = l_Lean_getAttributeImpl(v_env_3282_, v___x_3284_);
v___x_3286_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3285_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v_add_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v_add_3288_ = lean_ctor_get(v_a_3287_, 1);
lean_inc_ref(v_add_3288_);
lean_dec(v_a_3287_);
v___x_3289_ = lean_box(v_attrKind_3277_);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc(v_stx_3276_);
lean_inc(v_declName_3275_);
v___x_3290_ = lean_apply_6(v_add_3288_, v_declName_3275_, v_stx_3276_, v___x_3289_, v___y_3278_, v___y_3279_, lean_box(0));
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3315_; 
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v___x_3290_, 0);
lean_dec(v_unused_3316_);
v___x_3292_ = v___x_3290_;
v_isShared_3293_ = v_isSharedCheck_3315_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v___x_3290_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3315_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_symIntToBitVecName));
v___x_3295_ = l_Lean_getAttributeImpl(v_env_3282_, v___x_3294_);
v___x_3296_ = l_IO_ofExcept___at___00__private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__spec__0___redArg(v___x_3295_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v_add_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_del_object(v___x_3292_);
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v_add_3298_ = lean_ctor_get(v_a_3297_, 1);
lean_inc_ref(v_add_3298_);
lean_dec(v_a_3297_);
v___x_3299_ = lean_box(v_attrKind_3277_);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
v___x_3300_ = lean_apply_6(v_add_3298_, v_declName_3275_, v_stx_3276_, v___x_3299_, v___y_3278_, v___y_3279_, lean_box(0));
return v___x_3300_;
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_stx_3276_);
lean_dec(v_declName_3275_);
v_a_3301_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3303_ = v___x_3296_;
v_isShared_3304_ = v_isSharedCheck_3314_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3296_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3314_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3305_ = lean_io_error_to_string(v_a_3301_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 3);
lean_ctor_set(v___x_3292_, 0, v___x_3305_);
v___x_3307_ = v___x_3292_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3308_ = l_Lean_MessageData_ofFormat(v___x_3307_);
lean_inc(v_ref_3283_);
v___x_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_ref_3283_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3309_);
v___x_3311_ = v___x_3303_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
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
}
else
{
lean_dec_ref(v_env_3282_);
lean_dec(v_stx_3276_);
lean_dec(v_declName_3275_);
return v___x_3290_;
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3328_; 
lean_dec_ref(v_env_3282_);
lean_dec(v_stx_3276_);
lean_dec(v_declName_3275_);
v_a_3317_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3319_ = v___x_3286_;
v_isShared_3320_ = v_isSharedCheck_3328_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3286_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3328_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3321_ = lean_io_error_to_string(v_a_3317_);
v___x_3322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
v___x_3323_ = l_Lean_MessageData_ofFormat(v___x_3322_);
lean_inc(v_ref_3283_);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_ref_3283_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3324_);
v___x_3326_ = v___x_3319_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_declName_3329_, lean_object* v_stx_3330_, lean_object* v_attrKind_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
uint8_t v_attrKind_boxed_3335_; lean_object* v_res_3336_; 
v_attrKind_boxed_3335_ = lean_unbox(v_attrKind_3331_);
v_res_3336_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v_declName_3329_, v_stx_3330_, v_attrKind_boxed_3335_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
return v_res_3336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3339_ = l_Lean_stringToMessageData(v___x_3338_);
return v___x_3339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__2_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3342_ = l_Lean_stringToMessageData(v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(lean_object* v___x_3343_, lean_object* v_decl_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3349_ = l_Lean_MessageData_ofName(v___x_3343_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1___closed__3_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Tactic_BVDecide_isPotentialTypeAnalysisType_spec__0_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v___x_3352_, v___y_3345_, v___y_3346_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v___x_3354_, lean_object* v_decl_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___lam__1_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(v___x_3354_, v_decl_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v_decl_3355_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn___closed__10_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_));
v___x_3390_ = l_Lean_registerBuiltinAttribute(v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2____boxed(lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Meta_Tactic_BVDecide_Attr_0__Lean_Meta_Tactic_BVDecide_initFn_00___x40_Lean_Meta_Tactic_BVDecide_Attr_846454893____hygCtx___hyg_2_();
return v_res_3392_;
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
