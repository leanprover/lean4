// Lean compiler output
// Module: Lean.Elab.Tactic.Do.VCGen.Basic
// Imports: public import Lean.Elab.Tactic.Simp public import Lean.Elab.Tactic.Do.Attr import Init.Omega import Lean.Elab.ConfigEval
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
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object*);
lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
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
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_shift(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalBoolItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "VCGen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 105, 233, 55, 174, 94, 97, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 68, 95, 253, 186, 119, 149, 40)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(72, 48, 76, 98, 214, 72, 44, 78)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 75, 207, 246, 76, 246, 41, 61)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 199, 152, 134, 144, 220, 55, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 201, 7, 192, 148, 72, 34, 31)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 45, 74, 93, 100, 247, 195, 97)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 79, 2, 134, 178, 227, 219, 79)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 89, 143, 116, 220, 103, 214, 162)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 134, 235, 227, 114, 41, 14, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(233, 201, 67, 63, 162, 209, 110, 96)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 127, 236, 20, 208, 60, 55, 183)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 24, 62, 169, 38, 41, 106, 27)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 43, 72, 80, 203, 37, 115, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(140, 159, 252, 240, 92, 57, 206, 59)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)(((size_t)(540456248) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(139, 232, 253, 244, 224, 124, 180, 190)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 201, 132, 188, 184, 197, 210, 173)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 139, 180, 129, 225, 59, 72, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(205, 187, 211, 38, 21, 229, 65, 67)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 145, 235, 80, 149, 84, 119, 130)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 186, 72, 71, 180, 239, 13, 70)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 197, 164, 82, 155, 28, 143, 213)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 107, .m_capacity = 107, .m_length = 106, .m_data = "this option has no effect; `mvcgen` reports a deprecation warning controlled by `linter.deprecated.syntax`"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2026-09-23"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "this option has no effect"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(217, 19, 39, 228, 182, 81, 226, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 41, 69, 108, 13, 191, 254, 76)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mvcgen_warning;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Config"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___boxed(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7;
static const lean_string_object l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Expression contains `sorry`:"};
static const lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2;
static const lean_closure_object l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "jp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "leave"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "stepLimit"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 49, 149, 7, 10, 60, 240, 239)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 152, 202, 139, 125, 6, 69, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 37, 172, 141, 181, 136, 108, 8)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(193, 70, 2, 82, 51, 3, 30, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 123, 177, 168, 195, 132, 224, 9)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "elimLets"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "errorOnMissingSpec"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(10, 226, 168, 6, 221, 105, 122, 19)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(203, 171, 238, 235, 95, 6, 75, 210)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 70, 17, 154, 2, 122, 181, 174)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 35, 146, 212, 201, 162, 158, 65)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value_aux_5),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(166, 217, 146, 51, 246, 70, 143, 72)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown metavariable "};
static const lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__0 = (const lean_object*)&l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM = (const lean_object*)&l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_isDuplicable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_isDuplicable___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_isDuplicable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_isDuplicable___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_isDuplicable___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_isDuplicable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_isDuplicable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_isDuplicable___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_isDuplicable___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_isDuplicable___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isDuplicable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_isJP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "__do_jp"};
static const lean_object* l_Lean_Elab_Tactic_Do_isJP___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_isJP___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_isJP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_isJP___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 121, 241, 59, 37, 189, 140, 219)}};
static const lean_object* l_Lean_Elab_Tactic_Do_isJP___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_isJP___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isJP___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "getNumJoinParams: residual joinTy not a forall: "};
static const lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpErase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 24, 229, 171, 59, 186, 144, 157)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpStar"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(125, 38, 251, 225, 228, 173, 11, 37)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Could not resolve spec theorem `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 1, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__9_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__11_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14_value),LEAN_SCALAR_PTR_LITERAL(49, 203, 120, 209, 69, 128, 204, 215)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "negConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__17_value),LEAN_SCALAR_PTR_LITERAL(196, 29, 29, 161, 247, 206, 181, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20_value),LEAN_SCALAR_PTR_LITERAL(56, 247, 87, 81, 188, 35, 250, 148)}};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_mkSpecContext___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__10_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__11_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__12_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "adding "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__35 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__35_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__37 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__37_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_92_ = 0;
v___x_93_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_94_ = l_Lean_registerTraceClass(v___x_91_, v___x_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_95_;
v_res_95_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_();
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2____boxed(lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_();
return v_res_97_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(4153898153u);
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_107_ = l_Lean_Name_num___override(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_109_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_110_ = l_Lean_Name_str___override(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_112_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_113_ = l_Lean_Name_str___override(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_116_ = l_Lean_Name_num___override(v___x_115_, v___x_114_);
return v___x_116_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_));
v___x_119_ = 0;
v___x_120_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_121_ = l_Lean_registerTraceClass(v___x_118_, v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_122_;
v_res_122_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_();
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2____boxed(lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_();
return v_res_124_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(lean_object* v_name_125_, lean_object* v_decl_126_, lean_object* v_ref_127_){
_start:
{
lean_object* v_defValue_129_; lean_object* v_descr_130_; lean_object* v_deprecation_x3f_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_defValue_129_ = lean_ctor_get(v_decl_126_, 0);
v_descr_130_ = lean_ctor_get(v_decl_126_, 1);
v_deprecation_x3f_131_ = lean_ctor_get(v_decl_126_, 2);
v___x_132_ = lean_alloc_ctor(1, 0, 1);
v___x_133_ = lean_unbox(v_defValue_129_);
lean_ctor_set_uint8(v___x_132_, 0, v___x_133_);
lean_inc(v_deprecation_x3f_131_);
lean_inc_ref(v_descr_130_);
lean_inc_n(v_name_125_, 2);
v___x_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_134_, 0, v_name_125_);
lean_ctor_set(v___x_134_, 1, v_ref_127_);
lean_ctor_set(v___x_134_, 2, v___x_132_);
lean_ctor_set(v___x_134_, 3, v_descr_130_);
lean_ctor_set(v___x_134_, 4, v_deprecation_x3f_131_);
v___x_135_ = lean_register_option(v_name_125_, v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_143_; 
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_144_);
v___x_137_ = v___x_135_;
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
else
{
lean_dec(v___x_135_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
lean_inc(v_defValue_129_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_name_125_);
lean_ctor_set(v___x_139_, 1, v_defValue_129_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_139_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_name_125_);
v_a_145_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_135_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_135_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_125_ = stack[0].m_obj;
lean_object* v_decl_126_ = stack[1].m_obj;
lean_object* v_ref_127_ = stack[2].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(v_name_125_, v_decl_126_, v_ref_127_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_154_, lean_object* v_decl_155_, lean_object* v_ref_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(v_name_154_, v_decl_155_, v_ref_156_);
lean_dec_ref(v_decl_155_);
return v_res_158_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_));
v___x_189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_));
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_));
v___x_191_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(v___x_188_, v___x_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_192_;
v_res_192_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_();
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4____boxed(lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl(lean_object* v_x_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_tag_nat(v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl___boxed(lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl(v_x_197_);
lean_dec(v_x_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(lean_object* v_t_199_, lean_object* v_k_200_){
_start:
{
if (lean_obj_tag(v_t_199_) == 0)
{
lean_object* v_n_201_; lean_object* v___x_202_; 
v_n_201_ = lean_ctor_get(v_t_199_, 0);
lean_inc(v_n_201_);
lean_dec_ref_known(v_t_199_, 1);
v___x_202_ = lean_apply_1(v_k_200_, v_n_201_);
return v___x_202_;
}
else
{
return v_k_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim(lean_object* v_motive_203_, lean_object* v_ctorIdx_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_k_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_205_, v_k_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___boxed(lean_object* v_motive_209_, lean_object* v_ctorIdx_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_k_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim(v_motive_209_, v_ctorIdx_210_, v_t_211_, v_h_212_, v_k_213_);
lean_dec(v_ctorIdx_210_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim___redArg(lean_object* v_t_215_, lean_object* v_limited_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_215_, v_limited_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim(lean_object* v_motive_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_limited_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_219_, v_limited_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim___redArg(lean_object* v_t_223_, lean_object* v_unlimited_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_223_, v_unlimited_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim(lean_object* v_motive_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_unlimited_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_227_, v_unlimited_229_);
return v___x_230_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v_n_233_; lean_object* v_n_234_; uint8_t v___x_235_; 
v_n_233_ = lean_ctor_get(v_x_231_, 0);
v_n_234_ = lean_ctor_get(v_x_232_, 0);
v___x_235_ = lean_nat_dec_eq(v_n_233_, v_n_234_);
return v___x_235_;
}
else
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
}
else
{
if (lean_obj_tag(v_x_232_) == 0)
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
else
{
uint8_t v___x_238_; 
v___x_238_ = 1;
return v___x_238_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_231_ = stack[0].m_obj;
lean_object* v_x_232_ = stack[1].m_obj;
uint8_t v_res_239_;
v_res_239_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_231_, v_x_232_);
stack->m_num = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq___boxed(lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_240_, v_x_241_);
lean_dec(v_x_241_);
lean_dec(v_x_240_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_244_, v_x_245_);
return v___x_246_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_instDecidableEqFuel_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_244_ = stack[0].m_obj;
lean_object* v_x_245_ = stack[1].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel(v_x_244_, v_x_245_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel___boxed(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel(v_x_248_, v_x_249_);
lean_dec(v_x_249_);
lean_dec(v_x_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_box(0);
v___x_253_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_252_);
return v___x_254_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_258_;
v_res_258_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_260_;
}
}
lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_262_ = stack[1].m_obj;
lean_object* v___y_263_ = stack[2].m_obj;
lean_object* v___y_264_ = stack[3].m_obj;
lean_object* v___y_265_ = stack[4].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(lean_box(0), v___y_262_, v___y_263_, v___y_264_, v___y_265_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(lean_object* v_msgData_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; lean_object* v_env_283_; uint8_t v___x_284_; lean_object* v_env_285_; lean_object* v___x_286_; lean_object* v_toCold_287_; lean_object* v_mctx_288_; lean_object* v_lctx_289_; lean_object* v_options_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_282_ = lean_st_ref_get(v___y_280_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc_ref(v_env_283_);
lean_dec(v___x_282_);
v___x_284_ = 0;
v_env_285_ = l_Lean_Environment_setRecordingDeps(v_env_283_, v___x_284_);
v___x_286_ = lean_st_ref_get(v___y_278_);
v_toCold_287_ = lean_ctor_get(v___y_279_, 0);
v_mctx_288_ = lean_ctor_get(v___x_286_, 0);
lean_inc_ref(v_mctx_288_);
lean_dec(v___x_286_);
v_lctx_289_ = lean_ctor_get(v___y_277_, 2);
v_options_290_ = lean_ctor_get(v_toCold_287_, 2);
lean_inc_ref(v_options_290_);
lean_inc_ref(v_lctx_289_);
v___x_291_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_291_, 0, v_env_285_);
lean_ctor_set(v___x_291_, 1, v_mctx_288_);
lean_ctor_set(v___x_291_, 2, v_lctx_289_);
lean_ctor_set(v___x_291_, 3, v_options_290_);
v___x_292_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v_msgData_276_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_276_ = stack[0].m_obj;
lean_object* v___y_277_ = stack[1].m_obj;
lean_object* v___y_278_ = stack[2].m_obj;
lean_object* v___y_279_ = stack[3].m_obj;
lean_object* v___y_280_ = stack[4].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msgData_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msgData_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_301_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_ref_308_; lean_object* v___x_309_; lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
v_ref_308_ = lean_ctor_get(v___y_305_, 2);
v___x_309_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_318_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
lean_inc(v_ref_308_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v_ref_308_);
lean_ctor_set(v___x_314_, 1, v_a_310_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 1);
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_302_ = stack[0].m_obj;
lean_object* v___y_303_ = stack[1].m_obj;
lean_object* v___y_304_ = stack[2].m_obj;
lean_object* v___y_305_ = stack[3].m_obj;
lean_object* v___y_306_ = stack[4].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(lean_object* v___x_331_, lean_object* v___x_332_, lean_object* v_ctor_333_, lean_object* v_args_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_454_ = lean_string_dec_eq(v_ctor_333_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec_ref(v___x_332_);
v___x_455_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_455_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_array_get_size(v_args_334_);
v___x_457_ = lean_unsigned_to_nat(8u);
v___x_458_ = lean_nat_dec_eq(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec_ref(v___x_332_);
v___x_459_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_460_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_459_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
goto v___jp_340_;
}
}
v___jp_340_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_341_);
lean_inc(v___x_342_);
v___x_343_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_342_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_345_);
lean_inc(v___x_346_);
v___x_347_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_346_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = lean_unsigned_to_nat(2u);
v___x_350_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_349_);
lean_inc(v___x_350_);
v___x_351_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_350_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = lean_unsigned_to_nat(3u);
v___x_354_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_353_);
lean_inc(v___x_354_);
v___x_355_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_354_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v_evalExpr_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v_evalExpr_357_ = lean_ctor_get(v___x_332_, 0);
lean_inc_ref(v_evalExpr_357_);
lean_dec_ref(v___x_332_);
v___x_358_ = lean_unsigned_to_nat(4u);
v___x_359_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_358_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
lean_inc(v___x_359_);
v___x_360_ = lean_apply_6(v_evalExpr_357_, v___x_359_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, lean_box(0));
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
v___x_362_ = lean_unsigned_to_nat(5u);
v___x_363_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_362_);
lean_inc(v___x_363_);
v___x_364_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_363_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
v___x_366_ = lean_unsigned_to_nat(6u);
v___x_367_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_366_);
lean_inc(v___x_367_);
v___x_368_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_367_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = lean_unsigned_to_nat(7u);
v___x_371_ = lean_array_get_borrowed(v___x_331_, v_args_334_, v___x_370_);
lean_inc(v___x_371_);
v___x_372_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_371_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_388_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_388_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_388_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_388_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; uint8_t v___x_378_; uint8_t v___x_379_; uint8_t v___x_380_; uint8_t v___x_381_; uint8_t v___x_382_; uint8_t v___x_383_; uint8_t v___x_384_; lean_object* v___x_386_; 
v___x_377_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_377_, 0, v_a_361_);
v___x_378_ = lean_unbox(v_a_344_);
lean_dec(v_a_344_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v___x_378_);
v___x_379_ = lean_unbox(v_a_348_);
lean_dec(v_a_348_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1 + 1, v___x_379_);
v___x_380_ = lean_unbox(v_a_352_);
lean_dec(v_a_352_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1 + 2, v___x_380_);
v___x_381_ = lean_unbox(v_a_356_);
lean_dec(v_a_356_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1 + 3, v___x_381_);
v___x_382_ = lean_unbox(v_a_365_);
lean_dec(v_a_365_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1 + 4, v___x_382_);
v___x_383_ = lean_unbox(v_a_369_);
lean_dec(v_a_369_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1 + 5, v___x_383_);
v___x_384_ = lean_unbox(v_a_373_);
lean_dec(v_a_373_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1 + 6, v___x_384_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_386_ = v___x_375_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_377_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_a_369_);
lean_dec(v_a_365_);
lean_dec(v_a_361_);
lean_dec(v_a_356_);
lean_dec(v_a_352_);
lean_dec(v_a_348_);
lean_dec(v_a_344_);
v_a_389_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_372_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_372_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_a_365_);
lean_dec(v_a_361_);
lean_dec(v_a_356_);
lean_dec(v_a_352_);
lean_dec(v_a_348_);
lean_dec(v_a_344_);
v_a_397_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_368_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_368_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_361_);
lean_dec(v_a_356_);
lean_dec(v_a_352_);
lean_dec(v_a_348_);
lean_dec(v_a_344_);
v_a_405_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_364_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_364_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_a_356_);
lean_dec(v_a_352_);
lean_dec(v_a_348_);
lean_dec(v_a_344_);
v_a_413_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_360_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_360_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v_a_352_);
lean_dec(v_a_348_);
lean_dec(v_a_344_);
lean_dec_ref(v___x_332_);
v_a_421_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_355_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_355_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_a_348_);
lean_dec(v_a_344_);
lean_dec_ref(v___x_332_);
v_a_429_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_351_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_351_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
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
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_a_344_);
lean_dec_ref(v___x_332_);
v_a_437_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_347_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_347_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v___x_332_);
v_a_445_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_343_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_343_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_331_ = stack[0].m_obj;
lean_object* v___x_332_ = stack[1].m_obj;
lean_object* v_ctor_333_ = stack[2].m_obj;
lean_object* v_args_334_ = stack[3].m_obj;
lean_object* v___y_335_ = stack[4].m_obj;
lean_object* v___y_336_ = stack[5].m_obj;
lean_object* v___y_337_ = stack[6].m_obj;
lean_object* v___y_338_ = stack[7].m_obj;
lean_object* v_res_469_;
v_res_469_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(v___x_331_, v___x_332_, v_ctor_333_, v_args_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v_ctor_472_, lean_object* v_args_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(v___x_470_, v___x_471_, v_ctor_472_, v_args_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec_ref(v_args_473_);
lean_dec_ref(v_ctor_472_);
lean_dec_ref(v___x_470_);
return v_res_479_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_481_ = l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___f_484_; 
v___x_482_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0);
v___x_483_ = l_Lean_instInhabitedExpr;
v___f_484_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___boxed), 9, 2);
lean_closure_set(v___f_484_, 0, v___x_483_);
lean_closure_set(v___f_484_, 1, v___x_482_);
return v___f_484_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___f_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___f_499_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1);
v___x_500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_501_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_500_, v___f_499_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
return v___x_501_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_493_ = stack[0].m_obj;
lean_object* v_a_494_ = stack[1].m_obj;
lean_object* v_a_495_ = stack[2].m_obj;
lean_object* v_a_496_ = stack[3].m_obj;
lean_object* v_a_497_ = stack[4].m_obj;
lean_object* v_res_502_;
v_res_502_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
return v_res_509_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_510_, lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
return v___x_517_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_511_ = stack[1].m_obj;
lean_object* v___y_512_ = stack[2].m_obj;
lean_object* v___y_513_ = stack[3].m_obj;
lean_object* v___y_514_ = stack[4].m_obj;
lean_object* v___y_515_ = stack[5].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(lean_box(0), v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_519_, lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_519_, v_msg_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_526_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_box(0);
v___x_529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_530_ = l_Lean_Expr_const___override(v___x_529_, v___x_528_);
return v___x_530_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2);
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__0));
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3);
return v___x_536_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(lean_object* v_e_537_, lean_object* v___y_538_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_Expr_hasMVar(v_e_537_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_e_537_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v_mctx_543_; lean_object* v___x_544_; lean_object* v_fst_545_; lean_object* v_snd_546_; lean_object* v___x_547_; lean_object* v_cache_548_; lean_object* v_zetaDeltaFVarIds_549_; lean_object* v_postponed_550_; lean_object* v_diag_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_560_; 
v___x_542_ = lean_st_ref_get(v___y_538_);
v_mctx_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc_ref(v_mctx_543_);
lean_dec(v___x_542_);
v___x_544_ = l_Lean_instantiateMVarsCore(v_mctx_543_, v_e_537_);
v_fst_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_fst_545_);
v_snd_546_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_546_);
lean_dec_ref(v___x_544_);
v___x_547_ = lean_st_ref_take(v___y_538_);
v_cache_548_ = lean_ctor_get(v___x_547_, 1);
v_zetaDeltaFVarIds_549_ = lean_ctor_get(v___x_547_, 2);
v_postponed_550_ = lean_ctor_get(v___x_547_, 3);
v_diag_551_ = lean_ctor_get(v___x_547_, 4);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v___x_547_, 0);
lean_dec(v_unused_561_);
v___x_553_ = v___x_547_;
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_diag_551_);
lean_inc(v_postponed_550_);
lean_inc(v_zetaDeltaFVarIds_549_);
lean_inc(v_cache_548_);
lean_dec(v___x_547_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v_snd_546_);
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_snd_546_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_cache_548_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_zetaDeltaFVarIds_549_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_postponed_550_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_diag_551_);
v___x_556_ = v_reuseFailAlloc_559_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_st_ref_put(v___y_538_, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_fst_545_);
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_537_ = stack[0].m_obj;
lean_object* v___y_538_ = stack[1].m_obj;
lean_object* v_res_562_;
v_res_562_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_e_537_, v___y_538_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg___boxed(lean_object* v_e_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_e_563_, v___y_564_);
lean_dec(v___y_564_);
return v_res_566_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_box(0);
v___x_568_ = l_Lean_Elab_abortTermExceptionId;
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
return v___x_569_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg(){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_573_;
v_res_573_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___boxed(lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
return v_res_575_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_box(1);
v___x_577_ = l_Lean_MessageData_ofFormat(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__2));
v___x_582_ = l_Lean_MessageData_ofFormat(v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
return v_x_583_;
}
else
{
lean_object* v_head_585_; lean_object* v_tail_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_608_; 
v_head_585_ = lean_ctor_get(v_x_584_, 0);
v_tail_586_ = lean_ctor_get(v_x_584_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_608_ == 0)
{
v___x_588_ = v_x_584_;
v_isShared_589_ = v_isSharedCheck_608_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_tail_586_);
lean_inc(v_head_585_);
lean_dec(v_x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_608_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_before_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_606_; 
v_before_590_ = lean_ctor_get(v_head_585_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_head_585_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_head_585_, 1);
lean_dec(v_unused_607_);
v___x_592_ = v_head_585_;
v_isShared_593_ = v_isSharedCheck_606_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_before_590_);
lean_dec(v_head_585_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_606_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 7);
lean_ctor_set(v___x_592_, 1, v___x_594_);
lean_ctor_set(v___x_592_, 0, v_x_583_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_x_583_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_605_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 7);
lean_ctor_set(v___x_588_, 1, v___x_597_);
lean_ctor_set(v___x_588_, 0, v___x_596_);
v___x_599_ = v___x_588_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_597_);
v___x_599_ = v_reuseFailAlloc_604_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_MessageData_ofSyntax(v_before_590_);
v___x_601_ = l_Lean_indentD(v___x_600_);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_599_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v_x_583_ = v___x_602_;
v_x_584_ = v_tail_586_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(lean_object* v_opts_609_, lean_object* v_opt_610_){
_start:
{
lean_object* v_name_611_; lean_object* v_defValue_612_; lean_object* v_map_613_; lean_object* v___x_614_; 
v_name_611_ = lean_ctor_get(v_opt_610_, 0);
v_defValue_612_ = lean_ctor_get(v_opt_610_, 1);
v_map_613_ = lean_ctor_get(v_opts_609_, 0);
v___x_614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_613_, v_name_611_);
if (lean_obj_tag(v___x_614_) == 0)
{
uint8_t v___x_615_; 
v___x_615_ = lean_unbox(v_defValue_612_);
return v___x_615_;
}
else
{
lean_object* v_val_616_; 
v_val_616_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_val_616_);
lean_dec_ref_known(v___x_614_, 1);
if (lean_obj_tag(v_val_616_) == 1)
{
uint8_t v_v_617_; 
v_v_617_ = lean_ctor_get_uint8(v_val_616_, 0);
lean_dec_ref_known(v_val_616_, 0);
return v_v_617_;
}
else
{
uint8_t v___x_618_; 
lean_dec(v_val_616_);
v___x_618_ = lean_unbox(v_defValue_612_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_609_ = stack[0].m_obj;
lean_object* v_opt_610_ = stack[1].m_obj;
uint8_t v_res_619_;
v_res_619_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(v_opts_609_, v_opt_610_);
stack->m_num = v_res_619_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6___boxed(lean_object* v_opts_620_, lean_object* v_opt_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(v_opts_620_, v_opt_621_);
lean_dec_ref(v_opt_621_);
lean_dec_ref(v_opts_620_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__1));
v___x_628_ = l_Lean_MessageData_ofFormat(v___x_627_);
return v___x_628_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(lean_object* v_msgData_629_, lean_object* v_macroStack_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_633_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_631_);
v___x_634_ = l_Lean_Elab_pp_macroStack;
v___x_635_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(v___x_633_, v___x_634_);
lean_dec_ref(v___x_633_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_dec(v_macroStack_630_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_msgData_629_);
return v___x_636_;
}
else
{
if (lean_obj_tag(v_macroStack_630_) == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_msgData_629_);
return v___x_637_;
}
else
{
lean_object* v_head_638_; lean_object* v_after_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_654_; 
v_head_638_ = lean_ctor_get(v_macroStack_630_, 0);
lean_inc(v_head_638_);
v_after_639_ = lean_ctor_get(v_head_638_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_head_638_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_head_638_, 0);
lean_dec(v_unused_655_);
v___x_641_ = v_head_638_;
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_after_639_);
lean_dec(v_head_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 7);
lean_ctor_set(v___x_641_, 1, v___x_643_);
lean_ctor_set(v___x_641_, 0, v_msgData_629_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_msgData_629_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_653_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_msgData_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_646_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_Lean_MessageData_ofSyntax(v_after_639_);
v___x_649_ = l_Lean_indentD(v___x_648_);
v_msgData_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_650_, 0, v___x_647_);
lean_ctor_set(v_msgData_650_, 1, v___x_649_);
v___x_651_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7(v_msgData_650_, v_macroStack_630_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_629_ = stack[0].m_obj;
lean_object* v_macroStack_630_ = stack[1].m_obj;
lean_object* v___y_631_ = stack[2].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_msgData_629_, v_macroStack_630_, v___y_631_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_657_, lean_object* v_macroStack_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_msgData_657_, v_macroStack_658_, v___y_659_);
lean_dec_ref(v___y_659_);
return v_res_661_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_ref_670_; lean_object* v_macroStack_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_ref_670_ = lean_ctor_get(v___y_667_, 2);
v_macroStack_671_ = lean_ctor_get(v___y_663_, 1);
v___x_672_ = l_Lean_Elab_getBetterRef(v_ref_670_, v_macroStack_671_);
v___x_673_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_662_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_673_);
lean_inc(v_macroStack_671_);
v___x_675_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_a_674_, v_macroStack_671_, v___y_667_);
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_672_);
lean_ctor_set(v___x_680_, 1, v_a_676_);
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 1);
lean_ctor_set(v___x_678_, 0, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_662_ = stack[0].m_obj;
lean_object* v___y_663_ = stack[1].m_obj;
lean_object* v___y_664_ = stack[2].m_obj;
lean_object* v___y_665_ = stack[3].m_obj;
lean_object* v___y_666_ = stack[4].m_obj;
lean_object* v___y_667_ = stack[5].m_obj;
lean_object* v___y_668_ = stack[6].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg___boxed(lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v_msg_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_694_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__0));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__2));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__4));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__6));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__8));
v___x_709_ = l_Lean_stringToMessageData(v___x_708_);
return v___x_709_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_718_; lean_object* v_evalExpr_719_; lean_object* v_expectedType_x3f_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_toCold_726_; lean_object* v_currRecDepth_727_; lean_object* v_ref_728_; uint16_t v_optionFlags_729_; uint8_t v_suppressElabErrors_730_; uint8_t v_isRecordingDeps_731_; uint8_t v___x_732_; lean_object* v_ref_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0);
v_evalExpr_719_ = lean_ctor_get(v___x_718_, 0);
v_expectedType_x3f_720_ = lean_ctor_get(v___x_718_, 1);
v___x_721_ = 1;
v___x_722_ = lean_box(0);
v___x_723_ = lean_box(v___x_721_);
v___x_724_ = lean_box(v___x_721_);
lean_inc(v_expectedType_x3f_720_);
lean_inc(v_stx_710_);
v___x_725_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_725_, 0, v_stx_710_);
lean_closure_set(v___x_725_, 1, v_expectedType_x3f_720_);
lean_closure_set(v___x_725_, 2, v___x_723_);
lean_closure_set(v___x_725_, 3, v___x_724_);
lean_closure_set(v___x_725_, 4, v___x_722_);
v_toCold_726_ = lean_ctor_get(v_a_715_, 0);
v_currRecDepth_727_ = lean_ctor_get(v_a_715_, 1);
v_ref_728_ = lean_ctor_get(v_a_715_, 2);
v_optionFlags_729_ = lean_ctor_get_uint16(v_a_715_, sizeof(void*)*3);
v_suppressElabErrors_730_ = lean_ctor_get_uint8(v_a_715_, sizeof(void*)*3 + 2);
v_isRecordingDeps_731_ = lean_ctor_get_uint8(v_a_715_, sizeof(void*)*3 + 3);
v___x_732_ = 1;
v_ref_733_ = l_Lean_replaceRef(v_stx_710_, v_ref_728_);
lean_dec(v_stx_710_);
lean_inc(v_currRecDepth_727_);
lean_inc_ref(v_toCold_726_);
v___x_734_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_734_, 0, v_toCold_726_);
lean_ctor_set(v___x_734_, 1, v_currRecDepth_727_);
lean_ctor_set(v___x_734_, 2, v_ref_733_);
lean_ctor_set_uint16(v___x_734_, sizeof(void*)*3, v_optionFlags_729_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*3 + 2, v_suppressElabErrors_730_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*3 + 3, v_isRecordingDeps_731_);
v___x_735_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_725_, v___x_732_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v___x_734_, v_a_716_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v_a_738_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; uint8_t v___y_762_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; uint8_t v___x_847_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_a_736_, v_a_714_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref(v___x_737_);
v___x_847_ = l_Lean_Expr_hasSorry(v_a_738_);
if (v___x_847_ == 0)
{
v___y_792_ = v_a_711_;
v___y_793_ = v_a_712_;
v___y_794_ = v_a_713_;
v___y_795_ = v_a_714_;
v___y_796_ = v___x_734_;
v___y_797_ = v_a_716_;
goto v___jp_791_;
}
else
{
uint8_t v___x_848_; 
v___x_848_ = l_Lean_Expr_hasSyntheticSorry(v_a_738_);
if (v___x_848_ == 0)
{
v___y_829_ = v_a_711_;
v___y_830_ = v_a_712_;
v___y_831_ = v_a_713_;
v___y_832_ = v_a_714_;
v___y_833_ = v___x_734_;
v___y_834_ = v_a_716_;
goto v___jp_828_;
}
else
{
lean_object* v___x_849_; lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_738_);
lean_dec_ref_known(v___x_734_, 3);
v___x_849_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
v___jp_739_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_747_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1);
v___x_748_ = l_Lean_indentExpr(v_a_738_);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___y_746_);
v___x_751_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_750_, v___y_742_, v___y_740_, v___y_741_, v___y_745_, v___y_744_, v___y_743_);
lean_dec_ref(v___y_744_);
return v___x_751_;
}
v___jp_752_:
{
if (v___y_762_ == 0)
{
if (lean_obj_tag(v___y_754_) == 0)
{
lean_dec_ref_known(v___y_754_, 2);
lean_dec_ref(v___y_758_);
lean_dec(v_a_738_);
return v___y_761_;
}
else
{
lean_object* v_id_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_777_; 
v_id_763_ = lean_ctor_get(v___y_754_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___y_754_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___y_754_, 1);
lean_dec(v_unused_778_);
v___x_765_ = v___y_754_;
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_id_763_);
lean_dec(v___y_754_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_instBEqInternalExceptionId_beq(v___y_755_, v_id_763_);
lean_dec(v_id_763_);
if (v___x_767_ == 0)
{
lean_del_object(v___x_765_);
lean_dec_ref(v___y_758_);
lean_dec(v_a_738_);
return v___y_761_;
}
else
{
lean_dec_ref(v___y_761_);
if (lean_obj_tag(v_expectedType_x3f_720_) == 1)
{
lean_object* v_val_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v_val_768_ = lean_ctor_get(v_expectedType_x3f_720_, 0);
v___x_769_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3);
lean_inc(v_val_768_);
v___x_770_ = l_Lean_MessageData_ofExpr(v_val_768_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 7);
lean_ctor_set(v___x_765_, 1, v___x_770_);
lean_ctor_set(v___x_765_, 0, v___x_769_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_775_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___y_740_ = v___y_753_;
v___y_741_ = v___y_757_;
v___y_742_ = v___y_756_;
v___y_743_ = v___y_759_;
v___y_744_ = v___y_758_;
v___y_745_ = v___y_760_;
v___y_746_ = v___x_774_;
goto v___jp_739_;
}
}
else
{
lean_object* v___x_776_; 
lean_del_object(v___x_765_);
v___x_776_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7);
v___y_740_ = v___y_753_;
v___y_741_ = v___y_757_;
v___y_742_ = v___y_756_;
v___y_743_ = v___y_759_;
v___y_744_ = v___y_758_;
v___y_745_ = v___y_760_;
v___y_746_ = v___x_776_;
goto v___jp_739_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_758_);
lean_dec_ref(v___y_754_);
lean_dec(v_a_738_);
return v___y_761_;
}
}
v___jp_779_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc_ref(v_evalExpr_719_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_783_);
lean_inc_ref(v___y_782_);
lean_inc(v_a_738_);
v___x_787_ = lean_apply_6(v_evalExpr_719_, v_a_738_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, lean_box(0));
if (lean_obj_tag(v___x_787_) == 0)
{
lean_dec_ref(v___y_784_);
lean_dec(v_a_738_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; uint8_t v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
v___x_789_ = l_Lean_Exception_isInterrupt(v_a_788_);
if (v___x_789_ == 0)
{
uint8_t v___x_790_; 
lean_inc(v_a_788_);
v___x_790_ = l_Lean_Exception_isRuntime(v_a_788_);
v___y_753_ = v___y_781_;
v___y_754_ = v_a_788_;
v___y_755_ = v___x_786_;
v___y_756_ = v___y_780_;
v___y_757_ = v___y_782_;
v___y_758_ = v___y_784_;
v___y_759_ = v___y_785_;
v___y_760_ = v___y_783_;
v___y_761_ = v___x_787_;
v___y_762_ = v___x_790_;
goto v___jp_752_;
}
else
{
v___y_753_ = v___y_781_;
v___y_754_ = v_a_788_;
v___y_755_ = v___x_786_;
v___y_756_ = v___y_780_;
v___y_757_ = v___y_782_;
v___y_758_ = v___y_784_;
v___y_759_ = v___y_785_;
v___y_760_ = v___y_783_;
v___y_761_ = v___x_787_;
v___y_762_ = v___x_789_;
goto v___jp_752_;
}
}
}
v___jp_791_:
{
lean_object* v___x_798_; 
lean_inc(v_a_738_);
v___x_798_ = l_Lean_Meta_getMVars(v_a_738_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_799_, v___x_722_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v_a_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; uint8_t v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v___x_802_ = lean_unbox(v_a_801_);
lean_dec(v_a_801_);
if (v___x_802_ == 0)
{
v___y_780_ = v___y_792_;
v___y_781_ = v___y_793_;
v___y_782_ = v___y_794_;
v___y_783_ = v___y_795_;
v___y_784_ = v___y_796_;
v___y_785_ = v___y_797_;
goto v___jp_779_;
}
else
{
lean_object* v___x_803_; lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v___y_796_);
lean_dec(v_a_738_);
v___x_803_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v___y_796_);
lean_dec(v_a_738_);
v_a_812_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_800_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_800_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v___y_796_);
lean_dec(v_a_738_);
v_a_820_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_798_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_798_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
v___jp_828_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v___x_835_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9);
v___x_836_ = l_Lean_indentExpr(v_a_738_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_837_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec_ref(v___y_833_);
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref_known(v___x_734_, 3);
v_a_858_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_735_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_735_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_710_ = stack[0].m_obj;
lean_object* v_a_711_ = stack[1].m_obj;
lean_object* v_a_712_ = stack[2].m_obj;
lean_object* v_a_713_ = stack[3].m_obj;
lean_object* v_a_714_ = stack[4].m_obj;
lean_object* v_a_715_ = stack[5].m_obj;
lean_object* v_a_716_ = stack[6].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(v_stx_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(v_stx_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
return v_res_875_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = lean_box(0);
v___x_880_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__1));
v___x_881_ = l_Lean_mkConst(v___x_880_, v___x_879_);
return v___x_881_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(lean_object* v_stx_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_toCold_891_; lean_object* v_currRecDepth_892_; lean_object* v_ref_893_; uint16_t v_optionFlags_894_; uint8_t v_suppressElabErrors_895_; uint8_t v_isRecordingDeps_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_ref_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toCold_891_ = lean_ctor_get(v_a_888_, 0);
v_currRecDepth_892_ = lean_ctor_get(v_a_888_, 1);
v_ref_893_ = lean_ctor_get(v_a_888_, 2);
v_optionFlags_894_ = lean_ctor_get_uint16(v_a_888_, sizeof(void*)*3);
v_suppressElabErrors_895_ = lean_ctor_get_uint8(v_a_888_, sizeof(void*)*3 + 2);
v_isRecordingDeps_896_ = lean_ctor_get_uint8(v_a_888_, sizeof(void*)*3 + 3);
v___x_897_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_898_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2);
v___x_899_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__3));
v_ref_900_ = l_Lean_replaceRef(v_stx_883_, v_ref_893_);
lean_inc(v_currRecDepth_892_);
lean_inc_ref(v_toCold_891_);
v___x_901_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_901_, 0, v_toCold_891_);
lean_ctor_set(v___x_901_, 1, v_currRecDepth_892_);
lean_ctor_set(v___x_901_, 2, v_ref_900_);
lean_ctor_set_uint16(v___x_901_, sizeof(void*)*3, v_optionFlags_894_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*3 + 2, v_suppressElabErrors_895_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*3 + 3, v_isRecordingDeps_896_);
lean_inc(v_stx_883_);
v___x_902_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v___x_898_, v___x_899_, v_stx_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v___x_901_, v_a_889_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref_known(v___x_901_, 3);
lean_dec(v_stx_883_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_911_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_fst_907_; lean_object* v___x_909_; 
v_fst_907_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_fst_907_);
lean_dec(v_a_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_fst_907_);
v___x_909_ = v___x_905_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_fst_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_926_; 
v_a_912_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_926_ == 0)
{
v___x_914_ = v___x_902_;
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_902_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_926_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
lean_inc(v_a_912_);
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_925_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
uint8_t v___y_919_; uint8_t v___x_923_; 
v___x_923_ = l_Lean_Exception_isInterrupt(v_a_912_);
if (v___x_923_ == 0)
{
uint8_t v___x_924_; 
lean_inc(v_a_912_);
v___x_924_ = l_Lean_Exception_isRuntime(v_a_912_);
v___y_919_ = v___x_924_;
goto v___jp_918_;
}
else
{
v___y_919_ = v___x_923_;
goto v___jp_918_;
}
v___jp_918_:
{
if (v___y_919_ == 0)
{
if (lean_obj_tag(v_a_912_) == 0)
{
lean_dec_ref_known(v_a_912_, 2);
lean_dec_ref_known(v___x_901_, 3);
lean_dec(v_stx_883_);
return v___x_917_;
}
else
{
lean_object* v_id_920_; uint8_t v___x_921_; 
v_id_920_ = lean_ctor_get(v_a_912_, 0);
lean_inc(v_id_920_);
lean_dec_ref_known(v_a_912_, 2);
v___x_921_ = l_Lean_instBEqInternalExceptionId_beq(v___x_897_, v_id_920_);
lean_dec(v_id_920_);
if (v___x_921_ == 0)
{
lean_dec_ref_known(v___x_901_, 3);
lean_dec(v_stx_883_);
return v___x_917_;
}
else
{
lean_object* v___x_922_; 
lean_dec_ref(v___x_917_);
v___x_922_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(v_stx_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v___x_901_, v_a_889_);
lean_dec_ref_known(v___x_901_, 3);
return v___x_922_;
}
}
}
else
{
lean_dec(v_a_912_);
lean_dec_ref_known(v___x_901_, 3);
lean_dec(v_stx_883_);
return v___x_917_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_883_ = stack[0].m_obj;
lean_object* v_a_884_ = stack[1].m_obj;
lean_object* v_a_885_ = stack[2].m_obj;
lean_object* v_a_886_ = stack[3].m_obj;
lean_object* v_a_887_ = stack[4].m_obj;
lean_object* v_a_888_ = stack[5].m_obj;
lean_object* v_a_889_ = stack[6].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(v_stx_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(v_stx_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
return v_res_936_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1);
v___x_938_ = l_Lean_MessageData_ofExpr(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0);
v___x_940_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_943_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_942_);
return v___x_944_;
}
}
lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(lean_object* v_stx_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_ty_x3f_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_toCold_959_; lean_object* v_currRecDepth_960_; lean_object* v_ref_961_; uint16_t v_optionFlags_962_; uint8_t v_suppressElabErrors_963_; uint8_t v_isRecordingDeps_964_; uint8_t v___x_965_; lean_object* v_ref_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_ty_x3f_953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2);
v___x_954_ = 1;
v___x_955_ = lean_box(0);
v___x_956_ = lean_box(v___x_954_);
v___x_957_ = lean_box(v___x_954_);
lean_inc(v_stx_945_);
v___x_958_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_958_, 0, v_stx_945_);
lean_closure_set(v___x_958_, 1, v_ty_x3f_953_);
lean_closure_set(v___x_958_, 2, v___x_956_);
lean_closure_set(v___x_958_, 3, v___x_957_);
lean_closure_set(v___x_958_, 4, v___x_955_);
v_toCold_959_ = lean_ctor_get(v_a_950_, 0);
v_currRecDepth_960_ = lean_ctor_get(v_a_950_, 1);
v_ref_961_ = lean_ctor_get(v_a_950_, 2);
v_optionFlags_962_ = lean_ctor_get_uint16(v_a_950_, sizeof(void*)*3);
v_suppressElabErrors_963_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*3 + 2);
v_isRecordingDeps_964_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*3 + 3);
v___x_965_ = 1;
v_ref_966_ = l_Lean_replaceRef(v_stx_945_, v_ref_961_);
lean_dec(v_stx_945_);
lean_inc(v_currRecDepth_960_);
lean_inc_ref(v_toCold_959_);
v___x_967_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_967_, 0, v_toCold_959_);
lean_ctor_set(v___x_967_, 1, v_currRecDepth_960_);
lean_ctor_set(v___x_967_, 2, v_ref_966_);
lean_ctor_set_uint16(v___x_967_, sizeof(void*)*3, v_optionFlags_962_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*3 + 2, v_suppressElabErrors_963_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*3 + 3, v_isRecordingDeps_964_);
v___x_968_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_958_, v___x_965_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v___x_967_, v_a_951_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v_a_971_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; uint8_t v___y_982_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; uint8_t v___x_1066_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_a_969_, v_a_949_);
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_970_);
v___x_1066_ = l_Lean_Expr_hasSorry(v_a_971_);
if (v___x_1066_ == 0)
{
v___y_1011_ = v_a_946_;
v___y_1012_ = v_a_947_;
v___y_1013_ = v_a_948_;
v___y_1014_ = v_a_949_;
v___y_1015_ = v___x_967_;
v___y_1016_ = v_a_951_;
goto v___jp_1010_;
}
else
{
uint8_t v___x_1067_; 
v___x_1067_ = l_Lean_Expr_hasSyntheticSorry(v_a_971_);
if (v___x_1067_ == 0)
{
v___y_1048_ = v_a_946_;
v___y_1049_ = v_a_947_;
v___y_1050_ = v_a_948_;
v___y_1051_ = v_a_949_;
v___y_1052_ = v___x_967_;
v___y_1053_ = v_a_951_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1068_; lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v_a_971_);
lean_dec_ref_known(v___x_967_, 3);
v___x_1068_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
v___jp_972_:
{
if (v___y_982_ == 0)
{
if (lean_obj_tag(v___y_975_) == 0)
{
lean_dec_ref_known(v___y_975_, 2);
lean_dec_ref(v___y_978_);
lean_dec(v_a_971_);
return v___y_973_;
}
else
{
lean_object* v_id_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_996_; 
v_id_983_ = lean_ctor_get(v___y_975_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___y_975_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v___y_975_, 1);
lean_dec(v_unused_997_);
v___x_985_ = v___y_975_;
v_isShared_986_ = v_isSharedCheck_996_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_id_983_);
lean_dec(v___y_975_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_996_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_instBEqInternalExceptionId_beq(v___y_979_, v_id_983_);
lean_dec(v_id_983_);
if (v___x_987_ == 0)
{
lean_del_object(v___x_985_);
lean_dec_ref(v___y_978_);
lean_dec(v_a_971_);
return v___y_973_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
lean_dec_ref(v___y_973_);
v___x_988_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2);
v___x_989_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1);
v___x_990_ = l_Lean_indentExpr(v_a_971_);
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 7);
lean_ctor_set(v___x_985_, 1, v___x_990_);
lean_ctor_set(v___x_985_, 0, v___x_989_);
v___x_992_ = v___x_985_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_995_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_988_);
v___x_994_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_993_, v___y_977_, v___y_976_, v___y_980_, v___y_974_, v___y_978_, v___y_981_);
lean_dec_ref(v___y_978_);
return v___x_994_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_978_);
lean_dec_ref(v___y_975_);
lean_dec(v_a_971_);
return v___y_973_;
}
}
v___jp_998_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_971_);
v___x_1006_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(v_a_971_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_dec_ref(v___y_1003_);
lean_dec(v_a_971_);
return v___x_1006_;
}
else
{
lean_object* v_a_1007_; uint8_t v___x_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
v___x_1008_ = l_Lean_Exception_isInterrupt(v_a_1007_);
if (v___x_1008_ == 0)
{
uint8_t v___x_1009_; 
lean_inc(v_a_1007_);
v___x_1009_ = l_Lean_Exception_isRuntime(v_a_1007_);
v___y_973_ = v___x_1006_;
v___y_974_ = v___y_1002_;
v___y_975_ = v_a_1007_;
v___y_976_ = v___y_1000_;
v___y_977_ = v___y_999_;
v___y_978_ = v___y_1003_;
v___y_979_ = v___x_1005_;
v___y_980_ = v___y_1001_;
v___y_981_ = v___y_1004_;
v___y_982_ = v___x_1009_;
goto v___jp_972_;
}
else
{
v___y_973_ = v___x_1006_;
v___y_974_ = v___y_1002_;
v___y_975_ = v_a_1007_;
v___y_976_ = v___y_1000_;
v___y_977_ = v___y_999_;
v___y_978_ = v___y_1003_;
v___y_979_ = v___x_1005_;
v___y_980_ = v___y_1001_;
v___y_981_ = v___y_1004_;
v___y_982_ = v___x_1008_;
goto v___jp_972_;
}
}
}
v___jp_1010_:
{
lean_object* v___x_1017_; 
lean_inc(v_a_971_);
v___x_1017_ = l_Lean_Meta_getMVars(v_a_971_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1018_, v___x_955_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v_a_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; uint8_t v___x_1021_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = lean_unbox(v_a_1020_);
lean_dec(v_a_1020_);
if (v___x_1021_ == 0)
{
v___y_999_ = v___y_1011_;
v___y_1000_ = v___y_1012_;
v___y_1001_ = v___y_1013_;
v___y_1002_ = v___y_1014_;
v___y_1003_ = v___y_1015_;
v___y_1004_ = v___y_1016_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v___y_1015_);
lean_dec(v_a_971_);
v___x_1022_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v___y_1015_);
lean_dec(v_a_971_);
v_a_1031_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1019_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1019_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v___y_1015_);
lean_dec(v_a_971_);
v_a_1039_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1017_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1017_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
v___jp_1047_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v___x_1054_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9);
v___x_1055_ = l_Lean_indentExpr(v_a_971_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_1056_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec_ref(v___y_1052_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref_known(v___x_967_, 3);
v_a_1077_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_968_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_968_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_945_ = stack[0].m_obj;
lean_object* v_a_946_ = stack[1].m_obj;
lean_object* v_a_947_ = stack[2].m_obj;
lean_object* v_a_948_ = stack[3].m_obj;
lean_object* v_a_949_ = stack[4].m_obj;
lean_object* v_a_950_ = stack[5].m_obj;
lean_object* v_a_951_ = stack[6].m_obj;
lean_object* v_res_1085_;
v_res_1085_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(v_stx_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
stack->m_obj
 = v_res_1085_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(v_stx_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
return v_res_1094_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(lean_object* v_config_1170_, lean_object* v_item_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_item_1180_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_1184_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1171_, v___x_1183_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1184_) == 0)
{
uint8_t v___x_1185_; 
lean_dec_ref_known(v___x_1184_, 1);
v___x_1185_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1171_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1186_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1171_);
lean_inc_ref(v_item_1171_);
v___x_1187_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1171_);
v___x_1188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__1));
v___x_1189_ = lean_string_dec_lt(v___x_1186_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_string_dec_eq(v___x_1186_, v___x_1188_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__2));
v___x_1192_ = lean_string_dec_eq(v___x_1186_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__3));
v___x_1194_ = lean_string_dec_eq(v___x_1186_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__4));
v___x_1196_ = lean_string_dec_eq(v___x_1186_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__5));
v___x_1198_ = lean_string_dec_eq(v___x_1186_, v___x_1197_);
lean_dec_ref(v___x_1186_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6));
v___x_1200_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1199_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1200_) == 0)
{
uint8_t v___x_1201_; 
lean_dec_ref_known(v___x_1200_, 1);
v___x_1201_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1201_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1202_; 
lean_dec_ref(v___x_1187_);
v___x_1202_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1225_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1225_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1225_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
uint8_t v_leave_1207_; uint8_t v_elimLets_1208_; uint8_t v_jp_1209_; lean_object* v_stepLimit_1210_; uint8_t v_errorOnMissingSpec_1211_; uint8_t v_debug_1212_; uint8_t v_internalize_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1224_; 
v_leave_1207_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 1);
v_elimLets_1208_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 2);
v_jp_1209_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 3);
v_stepLimit_1210_ = lean_ctor_get(v_config_1170_, 0);
v_errorOnMissingSpec_1211_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 4);
v_debug_1212_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 5);
v_internalize_1213_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 6);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1215_ = v_config_1170_;
v_isShared_1216_ = v_isSharedCheck_1224_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_stepLimit_1210_);
lean_dec(v_config_1170_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1224_;
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
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_stepLimit_1210_);
v___x_1218_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
uint8_t v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unbox(v_a_1203_);
lean_dec(v_a_1203_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1, v___x_1219_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1 + 1, v_leave_1207_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1 + 2, v_elimLets_1208_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1 + 3, v_jp_1209_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1211_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1 + 5, v_debug_1212_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*1 + 6, v_internalize_1213_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1218_);
v___x_1221_ = v___x_1205_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_config_1170_);
v_a_1226_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1202_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1202_);
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
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1234_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1200_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1200_);
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
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v___x_1186_);
v___x_1242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7));
v___x_1243_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1242_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1243_) == 0)
{
uint8_t v___x_1244_; 
lean_dec_ref_known(v___x_1243_, 1);
v___x_1244_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1244_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1245_; 
lean_dec_ref(v___x_1187_);
lean_inc_ref(v_item_1171_);
v___x_1245_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_value_1246_; lean_object* v___x_1247_; 
lean_dec_ref_known(v___x_1245_, 1);
v_value_1246_ = lean_ctor_get(v_item_1171_, 2);
lean_inc(v_value_1246_);
lean_dec_ref(v_item_1171_);
v___x_1247_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(v_value_1246_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1270_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1270_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1270_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
uint8_t v_trivial_1252_; uint8_t v_leave_1253_; uint8_t v_elimLets_1254_; uint8_t v_jp_1255_; uint8_t v_errorOnMissingSpec_1256_; uint8_t v_debug_1257_; uint8_t v_internalize_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1268_; 
v_trivial_1252_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1);
v_leave_1253_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 1);
v_elimLets_1254_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 2);
v_jp_1255_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 3);
v_errorOnMissingSpec_1256_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 4);
v_debug_1257_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 5);
v_internalize_1258_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 6);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v_config_1170_, 0);
lean_dec(v_unused_1269_);
v___x_1260_ = v_config_1170_;
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v_config_1170_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1268_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_a_1248_);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1, v_trivial_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1 + 1, v_leave_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1 + 2, v_elimLets_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1 + 3, v_jp_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1 + 5, v_debug_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*1 + 6, v_internalize_1258_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1263_);
v___x_1265_ = v___x_1250_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_config_1170_);
v_a_1271_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1247_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1247_);
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
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1279_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1245_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1245_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1287_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1243_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1243_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v___x_1186_);
v___x_1295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8));
v___x_1296_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1295_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1296_) == 0)
{
uint8_t v___x_1297_; 
lean_dec_ref_known(v___x_1296_, 1);
v___x_1297_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1297_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1298_; 
lean_dec_ref(v___x_1187_);
v___x_1298_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1321_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1321_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1321_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
uint8_t v_trivial_1303_; uint8_t v_elimLets_1304_; uint8_t v_jp_1305_; lean_object* v_stepLimit_1306_; uint8_t v_errorOnMissingSpec_1307_; uint8_t v_debug_1308_; uint8_t v_internalize_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1320_; 
v_trivial_1303_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1);
v_elimLets_1304_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 2);
v_jp_1305_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 3);
v_stepLimit_1306_ = lean_ctor_get(v_config_1170_, 0);
v_errorOnMissingSpec_1307_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 4);
v_debug_1308_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 5);
v_internalize_1309_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 6);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1311_ = v_config_1170_;
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_stepLimit_1306_);
lean_dec(v_config_1170_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1320_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_stepLimit_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*1, v_trivial_1303_);
v___x_1314_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
uint8_t v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*1 + 1, v___x_1315_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*1 + 2, v_elimLets_1304_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*1 + 3, v_jp_1305_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1307_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*1 + 5, v_debug_1308_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*1 + 6, v_internalize_1309_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1314_);
v___x_1317_ = v___x_1301_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1314_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_config_1170_);
v_a_1322_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1298_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1298_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1330_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1296_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1296_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v___x_1186_);
v___x_1338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9));
v___x_1339_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1338_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1339_) == 0)
{
uint8_t v___x_1340_; 
lean_dec_ref_known(v___x_1339_, 1);
v___x_1340_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1341_; 
lean_dec_ref(v___x_1187_);
v___x_1341_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1364_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1364_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1364_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v_trivial_1346_; uint8_t v_leave_1347_; uint8_t v_elimLets_1348_; lean_object* v_stepLimit_1349_; uint8_t v_errorOnMissingSpec_1350_; uint8_t v_debug_1351_; uint8_t v_internalize_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1363_; 
v_trivial_1346_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1);
v_leave_1347_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 1);
v_elimLets_1348_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 2);
v_stepLimit_1349_ = lean_ctor_get(v_config_1170_, 0);
v_errorOnMissingSpec_1350_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 4);
v_debug_1351_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 5);
v_internalize_1352_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 6);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1354_ = v_config_1170_;
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_stepLimit_1349_);
lean_dec(v_config_1170_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_stepLimit_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1362_, sizeof(void*)*1, v_trivial_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1362_, sizeof(void*)*1 + 1, v_leave_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1362_, sizeof(void*)*1 + 2, v_elimLets_1348_);
v___x_1357_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
uint8_t v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_unbox(v_a_1342_);
lean_dec(v_a_1342_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*1 + 3, v___x_1358_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1350_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*1 + 5, v_debug_1351_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*1 + 6, v_internalize_1352_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1357_);
v___x_1360_ = v___x_1344_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1357_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_config_1170_);
v_a_1365_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1341_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1341_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1373_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1339_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1339_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec_ref(v___x_1186_);
v___x_1381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10));
v___x_1382_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1381_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1382_) == 0)
{
uint8_t v___x_1383_; 
lean_dec_ref_known(v___x_1382_, 1);
v___x_1383_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1384_; 
lean_dec_ref(v___x_1187_);
v___x_1384_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1407_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1407_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1407_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
uint8_t v_trivial_1389_; uint8_t v_leave_1390_; uint8_t v_elimLets_1391_; uint8_t v_jp_1392_; lean_object* v_stepLimit_1393_; uint8_t v_errorOnMissingSpec_1394_; uint8_t v_debug_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1406_; 
v_trivial_1389_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1);
v_leave_1390_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 1);
v_elimLets_1391_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 2);
v_jp_1392_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 3);
v_stepLimit_1393_ = lean_ctor_get(v_config_1170_, 0);
v_errorOnMissingSpec_1394_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 4);
v_debug_1395_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 5);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1397_ = v_config_1170_;
v_isShared_1398_ = v_isSharedCheck_1406_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_stepLimit_1393_);
lean_dec(v_config_1170_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1406_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_stepLimit_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1405_, sizeof(void*)*1, v_trivial_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1405_, sizeof(void*)*1 + 1, v_leave_1390_);
lean_ctor_set_uint8(v_reuseFailAlloc_1405_, sizeof(void*)*1 + 2, v_elimLets_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1405_, sizeof(void*)*1 + 3, v_jp_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1405_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1405_, sizeof(void*)*1 + 5, v_debug_1395_);
v___x_1400_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
uint8_t v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = lean_unbox(v_a_1385_);
lean_dec(v_a_1385_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*1 + 6, v___x_1401_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1400_);
v___x_1403_ = v___x_1387_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1400_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_config_1170_);
v_a_1408_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1384_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1384_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1416_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1382_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1382_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__11));
v___x_1425_ = lean_string_dec_eq(v___x_1186_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__12));
v___x_1427_ = lean_string_dec_eq(v___x_1186_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__13));
v___x_1429_ = lean_string_dec_eq(v___x_1186_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__14));
v___x_1431_ = lean_string_dec_eq(v___x_1186_, v___x_1430_);
lean_dec_ref(v___x_1186_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15));
v___x_1433_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1432_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1433_) == 0)
{
uint8_t v___x_1434_; 
lean_dec_ref_known(v___x_1433_, 1);
v___x_1434_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1435_; 
lean_dec_ref(v___x_1187_);
v___x_1435_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1458_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1458_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1458_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
uint8_t v_trivial_1440_; uint8_t v_leave_1441_; uint8_t v_elimLets_1442_; uint8_t v_jp_1443_; lean_object* v_stepLimit_1444_; uint8_t v_debug_1445_; uint8_t v_internalize_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1457_; 
v_trivial_1440_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1);
v_leave_1441_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 1);
v_elimLets_1442_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 2);
v_jp_1443_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 3);
v_stepLimit_1444_ = lean_ctor_get(v_config_1170_, 0);
v_debug_1445_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 5);
v_internalize_1446_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 6);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1448_ = v_config_1170_;
v_isShared_1449_ = v_isSharedCheck_1457_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_stepLimit_1444_);
lean_dec(v_config_1170_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1457_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_stepLimit_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*1, v_trivial_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*1 + 1, v_leave_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*1 + 2, v_elimLets_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1456_, sizeof(void*)*1 + 3, v_jp_1443_);
v___x_1451_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
uint8_t v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = lean_unbox(v_a_1436_);
lean_dec(v_a_1436_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1 + 4, v___x_1452_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1 + 5, v_debug_1445_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1 + 6, v_internalize_1446_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1451_);
v___x_1454_ = v___x_1438_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1451_);
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
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v_config_1170_);
v_a_1459_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1435_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1435_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1467_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1433_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1433_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref(v___x_1186_);
v___x_1475_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16));
v___x_1476_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1475_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1476_) == 0)
{
uint8_t v___x_1477_; 
lean_dec_ref_known(v___x_1476_, 1);
v___x_1477_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1477_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1478_; 
lean_dec_ref(v___x_1187_);
v___x_1478_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1501_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1501_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1501_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
uint8_t v_trivial_1483_; uint8_t v_leave_1484_; uint8_t v_jp_1485_; lean_object* v_stepLimit_1486_; uint8_t v_errorOnMissingSpec_1487_; uint8_t v_debug_1488_; uint8_t v_internalize_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1500_; 
v_trivial_1483_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1);
v_leave_1484_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 1);
v_jp_1485_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 3);
v_stepLimit_1486_ = lean_ctor_get(v_config_1170_, 0);
v_errorOnMissingSpec_1487_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 4);
v_debug_1488_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 5);
v_internalize_1489_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 6);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1491_ = v_config_1170_;
v_isShared_1492_ = v_isSharedCheck_1500_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_stepLimit_1486_);
lean_dec(v_config_1170_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1500_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_stepLimit_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*1, v_trivial_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*1 + 1, v_leave_1484_);
v___x_1494_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
uint8_t v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_unbox(v_a_1479_);
lean_dec(v_a_1479_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*1 + 2, v___x_1495_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*1 + 3, v_jp_1485_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1487_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*1 + 5, v_debug_1488_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*1 + 6, v_internalize_1489_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1494_);
v___x_1497_ = v___x_1481_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1494_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec_ref(v_config_1170_);
v_a_1502_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1478_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1478_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1510_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1476_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1476_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v___x_1186_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17));
v___x_1519_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1171_, v___x_1518_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1519_) == 0)
{
uint8_t v___x_1520_; 
lean_dec_ref_known(v___x_1519_, 1);
v___x_1520_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1520_ == 0)
{
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1521_; 
lean_dec_ref(v___x_1187_);
v___x_1521_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1544_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1544_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1544_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
uint8_t v_trivial_1526_; uint8_t v_leave_1527_; uint8_t v_elimLets_1528_; uint8_t v_jp_1529_; lean_object* v_stepLimit_1530_; uint8_t v_errorOnMissingSpec_1531_; uint8_t v_internalize_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1543_; 
v_trivial_1526_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1);
v_leave_1527_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 1);
v_elimLets_1528_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 2);
v_jp_1529_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 3);
v_stepLimit_1530_ = lean_ctor_get(v_config_1170_, 0);
v_errorOnMissingSpec_1531_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 4);
v_internalize_1532_ = lean_ctor_get_uint8(v_config_1170_, sizeof(void*)*1 + 6);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_config_1170_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1534_ = v_config_1170_;
v_isShared_1535_ = v_isSharedCheck_1543_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_stepLimit_1530_);
lean_dec(v_config_1170_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1543_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_stepLimit_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*1, v_trivial_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*1 + 1, v_leave_1527_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*1 + 2, v_elimLets_1528_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*1 + 3, v_jp_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1531_);
v___x_1537_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
uint8_t v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = lean_unbox(v_a_1522_);
lean_dec(v_a_1522_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*1 + 5, v___x_1538_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*1 + 6, v_internalize_1532_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1537_);
v___x_1540_ = v___x_1524_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1537_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v_config_1170_);
v_a_1545_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1521_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1521_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v___x_1187_);
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1553_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1519_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1519_);
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
uint8_t v___x_1561_; 
lean_dec_ref(v___x_1186_);
lean_dec_ref(v_config_1170_);
v___x_1561_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1187_);
if (v___x_1561_ == 0)
{
lean_dec_ref(v_item_1171_);
v_item_1180_ = v___x_1187_;
goto v___jp_1179_;
}
else
{
lean_object* v_value_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v___x_1187_);
v_value_1562_ = lean_ctor_get(v_item_1171_, 2);
lean_inc(v_value_1562_);
lean_dec_ref(v_item_1171_);
v___x_1563_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(v_value_1562_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1563_;
}
}
}
}
else
{
lean_dec_ref(v_config_1170_);
v_item_1180_ = v_item_1171_;
goto v___jp_1179_;
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_item_1171_);
lean_dec_ref(v_config_1170_);
v_a_1564_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1184_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1184_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
v___jp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__0));
v___x_1182_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1180_, v___x_1181_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1182_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1170_ = stack[0].m_obj;
lean_object* v_item_1171_ = stack[1].m_obj;
lean_object* v___y_1172_ = stack[2].m_obj;
lean_object* v___y_1173_ = stack[3].m_obj;
lean_object* v___y_1174_ = stack[4].m_obj;
lean_object* v___y_1175_ = stack[5].m_obj;
lean_object* v___y_1176_ = stack[6].m_obj;
lean_object* v___y_1177_ = stack[7].m_obj;
lean_object* v_res_1572_;
v_res_1572_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(v_config_1170_, v_item_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
stack->m_obj
 = v_res_1572_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1573_, lean_object* v_item_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(v_config_1573_, v_item_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
return v_res_1582_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(lean_object* v_e_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_e_1585_, v___y_1589_);
return v___x_1593_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1585_ = stack[0].m_obj;
lean_object* v___y_1586_ = stack[1].m_obj;
lean_object* v___y_1587_ = stack[2].m_obj;
lean_object* v___y_1588_ = stack[3].m_obj;
lean_object* v___y_1589_ = stack[4].m_obj;
lean_object* v___y_1590_ = stack[5].m_obj;
lean_object* v___y_1591_ = stack[6].m_obj;
lean_object* v_res_1594_;
v_res_1594_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(v_e_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
stack->m_obj
 = v_res_1594_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_e_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(v_e_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1603_;
}
}
lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4(lean_object* v_00_u03b1_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
return v___x_1612_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1605_ = stack[1].m_obj;
lean_object* v___y_1606_ = stack[2].m_obj;
lean_object* v___y_1607_ = stack[3].m_obj;
lean_object* v___y_1608_ = stack[4].m_obj;
lean_object* v___y_1609_ = stack[5].m_obj;
lean_object* v___y_1610_ = stack[6].m_obj;
lean_object* v_res_1613_;
v_res_1613_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4(lean_box(0), v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
stack->m_obj
 = v_res_1613_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4(v_00_u03b1_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1622_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(lean_object* v_00_u03b1_1623_, lean_object* v_msg_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v_msg_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1624_ = stack[1].m_obj;
lean_object* v___y_1625_ = stack[2].m_obj;
lean_object* v___y_1626_ = stack[3].m_obj;
lean_object* v___y_1627_ = stack[4].m_obj;
lean_object* v___y_1628_ = stack[5].m_obj;
lean_object* v___y_1629_ = stack[6].m_obj;
lean_object* v___y_1630_ = stack[7].m_obj;
lean_object* v_res_1633_;
v_res_1633_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(lean_box(0), v_msg_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
stack->m_obj
 = v_res_1633_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_msg_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(v_00_u03b1_1634_, v_msg_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1643_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(lean_object* v_msgData_1644_, lean_object* v_macroStack_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_msgData_1644_, v_macroStack_1645_, v___y_1650_);
return v___x_1653_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1644_ = stack[0].m_obj;
lean_object* v_macroStack_1645_ = stack[1].m_obj;
lean_object* v___y_1646_ = stack[2].m_obj;
lean_object* v___y_1647_ = stack[3].m_obj;
lean_object* v___y_1648_ = stack[4].m_obj;
lean_object* v___y_1649_ = stack[5].m_obj;
lean_object* v___y_1650_ = stack[6].m_obj;
lean_object* v___y_1651_ = stack[7].m_obj;
lean_object* v_res_1654_;
v_res_1654_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(v_msgData_1644_, v_macroStack_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
stack->m_obj
 = v_res_1654_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___boxed(lean_object* v_msgData_1655_, lean_object* v_macroStack_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(v_msgData_1655_, v_macroStack_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1664_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_1667_ = l_Lean_mkConst(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0);
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(lean_object* v_cfg_1670_, lean_object* v_cfgItem_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1);
v___x_1680_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_1670_, v_cfgItem_1671_, v___x_1679_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v___x_1680_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1670_ = stack[0].m_obj;
lean_object* v_cfgItem_1671_ = stack[1].m_obj;
lean_object* v___y_1672_ = stack[2].m_obj;
lean_object* v___y_1673_ = stack[3].m_obj;
lean_object* v___y_1674_ = stack[4].m_obj;
lean_object* v___y_1675_ = stack[5].m_obj;
lean_object* v___y_1676_ = stack[6].m_obj;
lean_object* v___y_1677_ = stack[7].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(v_cfg_1670_, v_cfgItem_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
stack->m_obj
 = v_res_1681_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___boxed(lean_object* v_cfg_1682_, lean_object* v_cfgItem_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(v_cfg_1682_, v_cfgItem_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v_cfgItem_1683_);
return v_res_1691_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg(lean_object* v_cfg_1693_, lean_object* v_init_1694_, uint8_t v_logExceptions_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_onErr_1700_; lean_object* v_eval_1701_; 
v_onErr_1700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0));
v_eval_1701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___closed__0));
if (v_logExceptions_1695_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1701_, v_init_1694_, v_cfg_1693_, v_onErr_1700_, v_logExceptions_1695_, v_a_1697_, v_a_1698_);
return v___x_1702_;
}
else
{
uint8_t v_recover_1703_; lean_object* v___x_1704_; 
v_recover_1703_ = lean_ctor_get_uint8(v_a_1696_, sizeof(void*)*1);
v___x_1704_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1701_, v_init_1694_, v_cfg_1693_, v_onErr_1700_, v_recover_1703_, v_a_1697_, v_a_1698_);
return v___x_1704_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1693_ = stack[0].m_obj;
lean_object* v_init_1694_ = stack[1].m_obj;
uint8_t v_logExceptions_1695_ = stack[2].m_num;
lean_object* v_a_1696_ = stack[3].m_obj;
lean_object* v_a_1697_ = stack[4].m_obj;
lean_object* v_a_1698_ = stack[5].m_obj;
lean_object* v_res_1705_;
v_res_1705_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_cfg_1693_, v_init_1694_, v_logExceptions_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
stack->m_obj
 = v_res_1705_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___boxed(lean_object* v_cfg_1706_, lean_object* v_init_1707_, lean_object* v_logExceptions_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
uint8_t v_logExceptions_boxed_1713_; lean_object* v_res_1714_; 
v_logExceptions_boxed_1713_ = lean_unbox(v_logExceptions_1708_);
v_res_1714_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_cfg_1706_, v_init_1707_, v_logExceptions_boxed_1713_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec_ref(v_a_1709_);
return v_res_1714_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elabConfig(lean_object* v_cfg_1715_, lean_object* v_init_1716_, uint8_t v_logExceptions_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_cfg_1715_, v_init_1716_, v_logExceptions_1717_, v_a_1718_, v_a_1724_, v_a_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elabConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1715_ = stack[0].m_obj;
lean_object* v_init_1716_ = stack[1].m_obj;
uint8_t v_logExceptions_1717_ = stack[2].m_num;
lean_object* v_a_1718_ = stack[3].m_obj;
lean_object* v_a_1719_ = stack[4].m_obj;
lean_object* v_a_1720_ = stack[5].m_obj;
lean_object* v_a_1721_ = stack[6].m_obj;
lean_object* v_a_1722_ = stack[7].m_obj;
lean_object* v_a_1723_ = stack[8].m_obj;
lean_object* v_a_1724_ = stack[9].m_obj;
lean_object* v_a_1725_ = stack[10].m_obj;
lean_object* v_res_1728_;
v_res_1728_ = l_Lean_Elab_Tactic_Do_elabConfig(v_cfg_1715_, v_init_1716_, v_logExceptions_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
stack->m_obj
 = v_res_1728_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object* v_cfg_1729_, lean_object* v_init_1730_, lean_object* v_logExceptions_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
uint8_t v_logExceptions_boxed_1741_; lean_object* v_res_1742_; 
v_logExceptions_boxed_1741_ = lean_unbox(v_logExceptions_1731_);
v_res_1742_ = l_Lean_Elab_Tactic_Do_elabConfig(v_cfg_1729_, v_init_1730_, v_logExceptions_boxed_1741_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
return v_res_1742_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg(lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1748_; lean_object* v_fuel_1749_; 
v___x_1748_ = lean_st_ref_get(v_a_1743_);
v_fuel_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_fuel_1749_);
if (lean_obj_tag(v_fuel_1749_) == 0)
{
lean_object* v_simpState_1750_; lean_object* v_invariants_1751_; lean_object* v_vcs_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1774_; 
v_simpState_1750_ = lean_ctor_get(v___x_1748_, 1);
v_invariants_1751_ = lean_ctor_get(v___x_1748_, 2);
v_vcs_1752_ = lean_ctor_get(v___x_1748_, 3);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v___x_1748_, 0);
lean_dec(v_unused_1775_);
v___x_1754_ = v___x_1748_;
v_isShared_1755_ = v_isSharedCheck_1774_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_vcs_1752_);
lean_inc(v_invariants_1751_);
lean_inc(v_simpState_1750_);
lean_dec(v___x_1748_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1774_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_n_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1773_; 
v_n_1756_ = lean_ctor_get(v_fuel_1749_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_fuel_1749_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1758_ = v_fuel_1749_;
v_isShared_1759_ = v_isSharedCheck_1773_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_n_1756_);
lean_dec(v_fuel_1749_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1773_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_zero_1760_; uint8_t v_isZero_1761_; 
v_zero_1760_ = lean_unsigned_to_nat(0u);
v_isZero_1761_ = lean_nat_dec_eq(v_n_1756_, v_zero_1760_);
if (v_isZero_1761_ == 1)
{
lean_del_object(v___x_1758_);
lean_dec(v_n_1756_);
lean_del_object(v___x_1754_);
lean_dec_ref(v_vcs_1752_);
lean_dec_ref(v_invariants_1751_);
lean_dec_ref(v_simpState_1750_);
goto v___jp_1745_;
}
else
{
lean_object* v_one_1762_; lean_object* v_n_1763_; lean_object* v___x_1765_; 
v_one_1762_ = lean_unsigned_to_nat(1u);
v_n_1763_ = lean_nat_sub(v_n_1756_, v_one_1762_);
lean_dec(v_n_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v_n_1763_);
v___x_1765_ = v___x_1758_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_n_1763_);
v___x_1765_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1767_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1765_);
v___x_1767_ = v___x_1754_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_simpState_1750_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_invariants_1751_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_vcs_1752_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_st_ref_swap(v_a_1743_, v___x_1767_);
lean_dec(v___x_1769_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
return v___x_1770_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1748_);
goto v___jp_1745_;
}
v___jp_1745_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_box(0);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_burnOne___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1743_ = stack[0].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1743_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg___boxed(lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1777_);
lean_dec(v_a_1777_);
return v_res_1779_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_burnOne(lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1781_);
return v___x_1787_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_burnOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1780_ = stack[0].m_obj;
lean_object* v_a_1781_ = stack[1].m_obj;
lean_object* v_a_1782_ = stack[2].m_obj;
lean_object* v_a_1783_ = stack[3].m_obj;
lean_object* v_a_1784_ = stack[4].m_obj;
lean_object* v_a_1785_ = stack[5].m_obj;
lean_object* v_res_1788_;
v_res_1788_ = l_Lean_Elab_Tactic_Do_burnOne(v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
stack->m_obj
 = v_res_1788_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___boxed(lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Elab_Tactic_Do_burnOne(v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
return v_res_1796_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(lean_object* v_x_1797_, lean_object* v_k_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v_fuel_1807_; 
v___x_1806_ = lean_st_ref_get(v_a_1800_);
v_fuel_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_fuel_1807_);
lean_dec(v___x_1806_);
if (lean_obj_tag(v_fuel_1807_) == 0)
{
lean_object* v_n_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_n_1808_ = lean_ctor_get(v_fuel_1807_, 0);
lean_inc(v_n_1808_);
lean_dec_ref_known(v_fuel_1807_, 1);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_nat_dec_eq(v_n_1808_, v___x_1809_);
lean_dec(v_n_1808_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref(v_x_1797_);
lean_inc(v_a_1804_);
lean_inc_ref(v_a_1803_);
lean_inc(v_a_1802_);
lean_inc_ref(v_a_1801_);
lean_inc(v_a_1800_);
lean_inc_ref(v_a_1799_);
v___x_1811_ = lean_apply_7(v_k_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, lean_box(0));
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; 
lean_dec_ref(v_k_1798_);
lean_inc(v_a_1804_);
lean_inc_ref(v_a_1803_);
lean_inc(v_a_1802_);
lean_inc_ref(v_a_1801_);
lean_inc(v_a_1800_);
lean_inc_ref(v_a_1799_);
v___x_1812_ = lean_apply_7(v_x_1797_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, lean_box(0));
return v___x_1812_;
}
}
else
{
lean_object* v___x_1813_; 
lean_dec(v_fuel_1807_);
lean_dec_ref(v_x_1797_);
lean_inc(v_a_1804_);
lean_inc_ref(v_a_1803_);
lean_inc(v_a_1802_);
lean_inc_ref(v_a_1801_);
lean_inc(v_a_1800_);
lean_inc_ref(v_a_1799_);
v___x_1813_ = lean_apply_7(v_k_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, lean_box(0));
return v___x_1813_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1797_ = stack[0].m_obj;
lean_object* v_k_1798_ = stack[1].m_obj;
lean_object* v_a_1799_ = stack[2].m_obj;
lean_object* v_a_1800_ = stack[3].m_obj;
lean_object* v_a_1801_ = stack[4].m_obj;
lean_object* v_a_1802_ = stack[5].m_obj;
lean_object* v_a_1803_ = stack[6].m_obj;
lean_object* v_a_1804_ = stack[7].m_obj;
lean_object* v_res_1814_;
v_res_1814_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1797_, v_k_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
stack->m_obj
 = v_res_1814_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg___boxed(lean_object* v_x_1815_, lean_object* v_k_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1815_, v_k_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1824_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel(lean_object* v_00_u03b1_1825_, lean_object* v_x_1826_, lean_object* v_k_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1826_, v_k_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ifOutOfFuel_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1826_ = stack[1].m_obj;
lean_object* v_k_1827_ = stack[2].m_obj;
lean_object* v_a_1828_ = stack[3].m_obj;
lean_object* v_a_1829_ = stack[4].m_obj;
lean_object* v_a_1830_ = stack[5].m_obj;
lean_object* v_a_1831_ = stack[6].m_obj;
lean_object* v_a_1832_ = stack[7].m_obj;
lean_object* v_a_1833_ = stack[8].m_obj;
lean_object* v_res_1836_;
v_res_1836_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel(lean_box(0), v_x_1826_, v_k_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
stack->m_obj
 = v_res_1836_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_x_1838_, lean_object* v_k_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel(v_00_u03b1_1837_, v_x_1838_, v_k_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v_ks_1852_; lean_object* v_vs_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1877_; 
v_ks_1852_ = lean_ctor_get(v_x_1848_, 0);
v_vs_1853_ = lean_ctor_get(v_x_1848_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_x_1848_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1855_ = v_x_1848_;
v_isShared_1856_ = v_isSharedCheck_1877_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_vs_1853_);
lean_inc(v_ks_1852_);
lean_dec(v_x_1848_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1877_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = lean_array_get_size(v_ks_1852_);
v___x_1858_ = lean_nat_dec_lt(v_x_1849_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_dec(v_x_1849_);
v___x_1859_ = lean_array_push(v_ks_1852_, v_x_1850_);
v___x_1860_ = lean_array_push(v_vs_1853_, v_x_1851_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1860_);
lean_ctor_set(v___x_1855_, 0, v___x_1859_);
v___x_1862_ = v___x_1855_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
else
{
lean_object* v_k_x27_1864_; uint8_t v___x_1865_; 
v_k_x27_1864_ = lean_array_fget_borrowed(v_ks_1852_, v_x_1849_);
v___x_1865_ = l_Lean_instBEqMVarId_beq(v_x_1850_, v_k_x27_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1867_; 
if (v_isShared_1856_ == 0)
{
v___x_1867_ = v___x_1855_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_ks_1852_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_vs_1853_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = lean_nat_add(v_x_1849_, v___x_1868_);
lean_dec(v_x_1849_);
v_x_1848_ = v___x_1867_;
v_x_1849_ = v___x_1869_;
goto _start;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1872_ = lean_array_fset(v_ks_1852_, v_x_1849_, v_x_1850_);
v___x_1873_ = lean_array_fset(v_vs_1853_, v_x_1849_, v_x_1851_);
lean_dec(v_x_1849_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1873_);
lean_ctor_set(v___x_1855_, 0, v___x_1872_);
v___x_1875_ = v___x_1855_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1873_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_n_1878_, lean_object* v_k_1879_, lean_object* v_v_1880_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_n_1878_, v___x_1881_, v_k_1879_, v_v_1880_);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1883_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1884_, size_t v_x_1885_, size_t v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
if (lean_obj_tag(v_x_1884_) == 0)
{
lean_object* v_es_1889_; size_t v___x_1890_; size_t v___x_1891_; lean_object* v_j_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_es_1889_ = lean_ctor_get(v_x_1884_, 0);
v___x_1890_ = ((size_t)31ULL);
v___x_1891_ = lean_usize_land(v_x_1885_, v___x_1890_);
v_j_1892_ = lean_usize_to_nat(v___x_1891_);
v___x_1893_ = lean_array_get_size(v_es_1889_);
v___x_1894_ = lean_nat_dec_lt(v_j_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_dec(v_j_1892_);
lean_dec(v_x_1888_);
lean_dec(v_x_1887_);
return v_x_1884_;
}
else
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1933_; 
lean_inc_ref(v_es_1889_);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_x_1884_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v_x_1884_, 0);
lean_dec(v_unused_1934_);
v___x_1896_ = v_x_1884_;
v_isShared_1897_ = v_isSharedCheck_1933_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_x_1884_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1933_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_v_1898_; lean_object* v___x_1899_; lean_object* v_xs_x27_1900_; lean_object* v___y_1902_; 
v_v_1898_ = lean_array_fget(v_es_1889_, v_j_1892_);
v___x_1899_ = lean_box(0);
v_xs_x27_1900_ = lean_array_fset(v_es_1889_, v_j_1892_, v___x_1899_);
switch(lean_obj_tag(v_v_1898_))
{
case 0:
{
lean_object* v_key_1907_; lean_object* v_val_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1918_; 
v_key_1907_ = lean_ctor_get(v_v_1898_, 0);
v_val_1908_ = lean_ctor_get(v_v_1898_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_v_1898_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1910_ = v_v_1898_;
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_val_1908_);
lean_inc(v_key_1907_);
lean_dec(v_v_1898_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_instBEqMVarId_beq(v_x_1887_, v_key_1907_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_del_object(v___x_1910_);
v___x_1913_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1907_, v_val_1908_, v_x_1887_, v_x_1888_);
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
v___y_1902_ = v___x_1914_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1916_; 
lean_dec(v_val_1908_);
lean_dec(v_key_1907_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_x_1888_);
lean_ctor_set(v___x_1910_, 0, v_x_1887_);
v___x_1916_ = v___x_1910_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_x_1887_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_x_1888_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
v___y_1902_ = v___x_1916_;
goto v___jp_1901_;
}
}
}
}
case 1:
{
lean_object* v_node_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1931_; 
v_node_1919_ = lean_ctor_get(v_v_1898_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_v_1898_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1921_ = v_v_1898_;
v_isShared_1922_ = v_isSharedCheck_1931_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_node_1919_);
lean_dec(v_v_1898_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1931_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
size_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1923_ = ((size_t)5ULL);
v___x_1924_ = lean_usize_shift_right(v_x_1885_, v___x_1923_);
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_x_1886_, v___x_1925_);
v___x_1927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_node_1919_, v___x_1924_, v___x_1926_, v_x_1887_, v_x_1888_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1927_);
v___x_1929_ = v___x_1921_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
v___y_1902_ = v___x_1929_;
goto v___jp_1901_;
}
}
}
default: 
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_x_1887_);
lean_ctor_set(v___x_1932_, 1, v_x_1888_);
v___y_1902_ = v___x_1932_;
goto v___jp_1901_;
}
}
v___jp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = lean_array_fset(v_xs_x27_1900_, v_j_1892_, v___y_1902_);
lean_dec(v_j_1892_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1903_);
v___x_1905_ = v___x_1896_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
else
{
lean_object* v_ks_1935_; lean_object* v_vs_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1954_; 
v_ks_1935_ = lean_ctor_get(v_x_1884_, 0);
v_vs_1936_ = lean_ctor_get(v_x_1884_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_x_1884_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1938_ = v_x_1884_;
v_isShared_1939_ = v_isSharedCheck_1954_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_vs_1936_);
lean_inc(v_ks_1935_);
lean_dec(v_x_1884_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1954_;
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
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_ks_1935_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_vs_1936_);
v___x_1941_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v_newNode_1942_; size_t v___x_1943_; uint8_t v___x_1944_; 
v_newNode_1942_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v___x_1941_, v_x_1887_, v_x_1888_);
v___x_1943_ = ((size_t)7ULL);
v___x_1944_ = lean_usize_dec_le(v___x_1943_, v_x_1886_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1945_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1942_);
v___x_1946_ = lean_unsigned_to_nat(4u);
v___x_1947_ = lean_nat_dec_lt(v___x_1945_, v___x_1946_);
lean_dec(v___x_1945_);
if (v___x_1947_ == 0)
{
lean_object* v_ks_1948_; lean_object* v_vs_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_ks_1948_ = lean_ctor_get(v_newNode_1942_, 0);
lean_inc_ref(v_ks_1948_);
v_vs_1949_ = lean_ctor_get(v_newNode_1942_, 1);
lean_inc_ref(v_vs_1949_);
lean_dec_ref(v_newNode_1942_);
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1952_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_x_1886_, v_ks_1948_, v_vs_1949_, v___x_1950_, v___x_1951_);
lean_dec_ref(v_vs_1949_);
lean_dec_ref(v_ks_1948_);
return v___x_1952_;
}
else
{
return v_newNode_1942_;
}
}
else
{
return v_newNode_1942_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1884_ = stack[0].m_obj;
size_t v_x_1885_ = stack[1].m_num;
size_t v_x_1886_ = stack[2].m_num;
lean_object* v_x_1887_ = stack[3].m_obj;
lean_object* v_x_1888_ = stack[4].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1884_, v_x_1885_, v_x_1886_, v_x_1887_, v_x_1888_);
stack->m_obj
 = v_res_1955_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(size_t v_depth_1956_, lean_object* v_keys_1957_, lean_object* v_vals_1958_, lean_object* v_i_1959_, lean_object* v_entries_1960_){
_start:
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = lean_array_get_size(v_keys_1957_);
v___x_1962_ = lean_nat_dec_lt(v_i_1959_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_dec(v_i_1959_);
return v_entries_1960_;
}
else
{
lean_object* v_k_1963_; lean_object* v_v_1964_; uint64_t v___x_1965_; size_t v_h_1966_; size_t v___x_1967_; lean_object* v___x_1968_; size_t v___x_1969_; size_t v___x_1970_; size_t v___x_1971_; size_t v_h_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_k_1963_ = lean_array_fget_borrowed(v_keys_1957_, v_i_1959_);
v_v_1964_ = lean_array_fget_borrowed(v_vals_1958_, v_i_1959_);
v___x_1965_ = l_Lean_instHashableMVarId_hash(v_k_1963_);
v_h_1966_ = lean_uint64_to_usize(v___x_1965_);
v___x_1967_ = ((size_t)5ULL);
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_sub(v_depth_1956_, v___x_1969_);
v___x_1971_ = lean_usize_mul(v___x_1967_, v___x_1970_);
v_h_1972_ = lean_usize_shift_right(v_h_1966_, v___x_1971_);
v___x_1973_ = lean_nat_add(v_i_1959_, v___x_1968_);
lean_dec(v_i_1959_);
lean_inc(v_v_1964_);
lean_inc(v_k_1963_);
v___x_1974_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_entries_1960_, v_h_1972_, v_depth_1956_, v_k_1963_, v_v_1964_);
v_i_1959_ = v___x_1973_;
v_entries_1960_ = v___x_1974_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1956_ = stack[0].m_num;
lean_object* v_keys_1957_ = stack[1].m_obj;
lean_object* v_vals_1958_ = stack[2].m_obj;
lean_object* v_i_1959_ = stack[3].m_obj;
lean_object* v_entries_1960_ = stack[4].m_obj;
lean_object* v_res_1976_;
v_res_1976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_1956_, v_keys_1957_, v_vals_1958_, v_i_1959_, v_entries_1960_);
stack->m_obj
 = v_res_1976_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_1977_, lean_object* v_keys_1978_, lean_object* v_vals_1979_, lean_object* v_i_1980_, lean_object* v_entries_1981_){
_start:
{
size_t v_depth_boxed_1982_; lean_object* v_res_1983_; 
v_depth_boxed_1982_ = lean_unbox_usize(v_depth_1977_);
lean_dec(v_depth_1977_);
v_res_1983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_boxed_1982_, v_keys_1978_, v_vals_1979_, v_i_1980_, v_entries_1981_);
lean_dec_ref(v_vals_1979_);
lean_dec_ref(v_keys_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
size_t v_x_7222__boxed_1989_; size_t v_x_7223__boxed_1990_; lean_object* v_res_1991_; 
v_x_7222__boxed_1989_ = lean_unbox_usize(v_x_1985_);
lean_dec(v_x_1985_);
v_x_7223__boxed_1990_ = lean_unbox_usize(v_x_1986_);
lean_dec(v_x_1986_);
v_res_1991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1984_, v_x_7222__boxed_1989_, v_x_7223__boxed_1990_, v_x_1987_, v_x_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
uint64_t v___x_1995_; size_t v___x_1996_; size_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = l_Lean_instHashableMVarId_hash(v_x_1993_);
v___x_1996_ = lean_uint64_to_usize(v___x_1995_);
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1992_, v___x_1996_, v___x_1997_, v_x_1993_, v_x_1994_);
return v___x_1998_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(lean_object* v_range_1999_, lean_object* v_b_2000_, lean_object* v_i_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_stop_2005_; lean_object* v_step_2006_; lean_object* v_a_2008_; lean_object* v___y_2012_; uint8_t v___x_2028_; 
v_stop_2005_ = lean_ctor_get(v_range_1999_, 1);
v_step_2006_ = lean_ctor_get(v_range_1999_, 2);
v___x_2028_ = lean_nat_dec_lt(v_i_2001_, v_stop_2005_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_dec(v_i_2001_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_b_2000_);
return v___x_2029_;
}
else
{
lean_object* v_decls_2030_; lean_object* v_size_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_decls_2030_ = lean_ctor_get(v_b_2000_, 1);
v_size_2031_ = lean_ctor_get(v_decls_2030_, 2);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_nat_dec_lt(v_i_2001_, v_size_2031_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = l_outOfBounds___redArg(v___x_2032_);
v___y_2012_ = v___x_2034_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2032_, v_decls_2030_, v_i_2001_);
v___y_2012_ = v___x_2035_;
goto v___jp_2011_;
}
}
v___jp_2007_:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_nat_add(v_i_2001_, v_step_2006_);
lean_dec(v_i_2001_);
v_b_2000_ = v_a_2008_;
v_i_2001_ = v___x_2009_;
goto _start;
}
v___jp_2011_:
{
if (lean_obj_tag(v___y_2012_) == 1)
{
lean_object* v_val_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_val_2013_ = lean_ctor_get(v___y_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v___y_2012_, 1);
v___x_2014_ = l_Lean_LocalDecl_userName(v_val_2013_);
v___x_2015_ = l_Lean_Name_hasMacroScopes(v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Core_mkFreshUserName(v___x_2014_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l_Lean_LocalDecl_fvarId(v_val_2013_);
lean_dec(v_val_2013_);
v___x_2019_ = l_Lean_LocalContext_setUserName(v_b_2000_, v___x_2018_, v_a_2017_);
v_a_2008_ = v___x_2019_;
goto v___jp_2007_;
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_val_2013_);
lean_dec(v_i_2001_);
lean_dec_ref(v_b_2000_);
v_a_2020_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2016_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2016_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_dec(v___x_2014_);
lean_dec(v_val_2013_);
v_a_2008_ = v_b_2000_;
goto v___jp_2007_;
}
}
else
{
lean_dec(v___y_2012_);
v_a_2008_ = v_b_2000_;
goto v___jp_2007_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_1999_ = stack[0].m_obj;
lean_object* v_b_2000_ = stack[1].m_obj;
lean_object* v_i_2001_ = stack[2].m_obj;
lean_object* v___y_2002_ = stack[3].m_obj;
lean_object* v___y_2003_ = stack[4].m_obj;
lean_object* v_res_2036_;
v_res_2036_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_1999_, v_b_2000_, v_i_2001_, v___y_2002_, v___y_2003_);
stack->m_obj
 = v_res_2036_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_range_2037_, lean_object* v_b_2038_, lean_object* v_i_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_2037_, v_b_2038_, v_i_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v_range_2037_);
return v_res_2043_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(lean_object* v_lctx_2044_, lean_object* v_idx_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_inc_ref(v_lctx_2044_);
v___x_2053_ = lean_local_ctx_num_indices(v_lctx_2044_);
v___x_2054_ = lean_unsigned_to_nat(1u);
lean_inc(v_idx_2045_);
v___x_2055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2055_, 0, v_idx_2045_);
lean_ctor_set(v___x_2055_, 1, v___x_2053_);
lean_ctor_set(v___x_2055_, 2, v___x_2054_);
v___x_2056_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v___x_2055_, v_lctx_2044_, v_idx_2045_, v___y_2050_, v___y_2051_);
lean_dec_ref_known(v___x_2055_, 3);
return v___x_2056_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_2044_ = stack[0].m_obj;
lean_object* v_idx_2045_ = stack[1].m_obj;
lean_object* v___y_2046_ = stack[2].m_obj;
lean_object* v___y_2047_ = stack[3].m_obj;
lean_object* v___y_2048_ = stack[4].m_obj;
lean_object* v___y_2049_ = stack[5].m_obj;
lean_object* v___y_2050_ = stack[6].m_obj;
lean_object* v___y_2051_ = stack[7].m_obj;
lean_object* v_res_2057_;
v_res_2057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_2044_, v_idx_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
stack->m_obj
 = v_res_2057_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0___boxed(lean_object* v_lctx_2058_, lean_object* v_idx_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_2058_, v_idx_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2067_;
}
}
static lean_object* _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = ((lean_object*)(l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__0));
v___x_2070_ = l_Lean_stringToMessageData(v___x_2069_);
return v___x_2070_;
}
}
lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(lean_object* v_mvarId_2071_, lean_object* v_idx_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; lean_object* v_mctx_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_st_ref_get(v___y_2076_);
v_mctx_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_ref(v_mctx_2081_);
lean_dec(v___x_2080_);
v___x_2082_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2081_, v_mvarId_2071_);
lean_dec_ref(v_mctx_2081_);
if (lean_obj_tag(v___x_2082_) == 1)
{
lean_object* v_val_2083_; lean_object* v_userName_2084_; lean_object* v_lctx_2085_; lean_object* v_type_2086_; lean_object* v_depth_2087_; lean_object* v_localInstances_2088_; uint8_t v_kind_2089_; lean_object* v_numScopeArgs_2090_; lean_object* v_index_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2150_; 
v_val_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v_userName_2084_ = lean_ctor_get(v_val_2083_, 0);
v_lctx_2085_ = lean_ctor_get(v_val_2083_, 1);
v_type_2086_ = lean_ctor_get(v_val_2083_, 2);
v_depth_2087_ = lean_ctor_get(v_val_2083_, 3);
v_localInstances_2088_ = lean_ctor_get(v_val_2083_, 4);
v_kind_2089_ = lean_ctor_get_uint8(v_val_2083_, sizeof(void*)*7);
v_numScopeArgs_2090_ = lean_ctor_get(v_val_2083_, 5);
v_index_2091_ = lean_ctor_get(v_val_2083_, 6);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_val_2083_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2093_ = v_val_2083_;
v_isShared_2094_ = v_isSharedCheck_2150_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_index_2091_);
lean_inc(v_numScopeArgs_2090_);
lean_inc(v_localInstances_2088_);
lean_inc(v_depth_2087_);
lean_inc(v_type_2086_);
lean_inc(v_lctx_2085_);
lean_inc(v_userName_2084_);
lean_dec(v_val_2083_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2150_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; 
v___x_2095_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_2085_, v_idx_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2141_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2141_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2141_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; lean_object* v_mctx_2101_; lean_object* v_cache_2102_; lean_object* v_zetaDeltaFVarIds_2103_; lean_object* v_postponed_2104_; lean_object* v_diag_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2140_; 
v___x_2100_ = lean_st_ref_take(v___y_2076_);
v_mctx_2101_ = lean_ctor_get(v___x_2100_, 0);
v_cache_2102_ = lean_ctor_get(v___x_2100_, 1);
v_zetaDeltaFVarIds_2103_ = lean_ctor_get(v___x_2100_, 2);
v_postponed_2104_ = lean_ctor_get(v___x_2100_, 3);
v_diag_2105_ = lean_ctor_get(v___x_2100_, 4);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2107_ = v___x_2100_;
v_isShared_2108_ = v_isSharedCheck_2140_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_diag_2105_);
lean_inc(v_postponed_2104_);
lean_inc(v_zetaDeltaFVarIds_2103_);
lean_inc(v_cache_2102_);
lean_inc(v_mctx_2101_);
lean_dec(v___x_2100_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2140_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_depth_2109_; lean_object* v_levelAssignDepth_2110_; lean_object* v_lmvarCounter_2111_; lean_object* v_mvarCounter_2112_; lean_object* v_lDecls_2113_; lean_object* v_decls_2114_; lean_object* v_userNames_2115_; lean_object* v_lAssignment_2116_; lean_object* v_eAssignment_2117_; lean_object* v_dAssignment_2118_; lean_object* v_instanceTypedMVars_2119_; lean_object* v_synthNormMemo_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2139_; 
v_depth_2109_ = lean_ctor_get(v_mctx_2101_, 0);
v_levelAssignDepth_2110_ = lean_ctor_get(v_mctx_2101_, 1);
v_lmvarCounter_2111_ = lean_ctor_get(v_mctx_2101_, 2);
v_mvarCounter_2112_ = lean_ctor_get(v_mctx_2101_, 3);
v_lDecls_2113_ = lean_ctor_get(v_mctx_2101_, 4);
v_decls_2114_ = lean_ctor_get(v_mctx_2101_, 5);
v_userNames_2115_ = lean_ctor_get(v_mctx_2101_, 6);
v_lAssignment_2116_ = lean_ctor_get(v_mctx_2101_, 7);
v_eAssignment_2117_ = lean_ctor_get(v_mctx_2101_, 8);
v_dAssignment_2118_ = lean_ctor_get(v_mctx_2101_, 9);
v_instanceTypedMVars_2119_ = lean_ctor_get(v_mctx_2101_, 10);
v_synthNormMemo_2120_ = lean_ctor_get(v_mctx_2101_, 11);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_mctx_2101_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2122_ = v_mctx_2101_;
v_isShared_2123_ = v_isSharedCheck_2139_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_synthNormMemo_2120_);
lean_inc(v_instanceTypedMVars_2119_);
lean_inc(v_dAssignment_2118_);
lean_inc(v_eAssignment_2117_);
lean_inc(v_lAssignment_2116_);
lean_inc(v_userNames_2115_);
lean_inc(v_decls_2114_);
lean_inc(v_lDecls_2113_);
lean_inc(v_mvarCounter_2112_);
lean_inc(v_lmvarCounter_2111_);
lean_inc(v_levelAssignDepth_2110_);
lean_inc(v_depth_2109_);
lean_dec(v_mctx_2101_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2139_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_box(0);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v_a_2096_);
v___x_2126_ = v___x_2093_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_userName_2084_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_a_2096_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_type_2086_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_depth_2087_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_localInstances_2088_);
lean_ctor_set(v_reuseFailAlloc_2138_, 5, v_numScopeArgs_2090_);
lean_ctor_set(v_reuseFailAlloc_2138_, 6, v_index_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2138_, sizeof(void*)*7, v_kind_2089_);
v___x_2126_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_decls_2114_, v_mvarId_2071_, v___x_2126_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 5, v___x_2127_);
v___x_2129_ = v___x_2122_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_depth_2109_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_levelAssignDepth_2110_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_lmvarCounter_2111_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v_mvarCounter_2112_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v_lDecls_2113_);
lean_ctor_set(v_reuseFailAlloc_2137_, 5, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2137_, 6, v_userNames_2115_);
lean_ctor_set(v_reuseFailAlloc_2137_, 7, v_lAssignment_2116_);
lean_ctor_set(v_reuseFailAlloc_2137_, 8, v_eAssignment_2117_);
lean_ctor_set(v_reuseFailAlloc_2137_, 9, v_dAssignment_2118_);
lean_ctor_set(v_reuseFailAlloc_2137_, 10, v_instanceTypedMVars_2119_);
lean_ctor_set(v_reuseFailAlloc_2137_, 11, v_synthNormMemo_2120_);
v___x_2129_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2129_);
v___x_2131_ = v___x_2107_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_cache_2102_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_zetaDeltaFVarIds_2103_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_postponed_2104_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_diag_2105_);
v___x_2131_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = lean_st_ref_put(v___y_2076_, v___x_2131_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2124_);
v___x_2134_ = v___x_2098_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2124_);
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
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_del_object(v___x_2093_);
lean_dec(v_index_2091_);
lean_dec(v_numScopeArgs_2090_);
lean_dec_ref(v_localInstances_2088_);
lean_dec(v_depth_2087_);
lean_dec_ref(v_type_2086_);
lean_dec(v_userName_2084_);
lean_dec(v_mvarId_2071_);
v_a_2142_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2095_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2095_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec(v___x_2082_);
lean_dec(v_idx_2072_);
v___x_2151_ = lean_obj_once(&l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1, &l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1_once, _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1);
v___x_2152_ = l_Lean_MessageData_ofName(v_mvarId_2071_);
v___x_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2153_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
return v___x_2154_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2071_ = stack[0].m_obj;
lean_object* v_idx_2072_ = stack[1].m_obj;
lean_object* v___y_2073_ = stack[2].m_obj;
lean_object* v___y_2074_ = stack[3].m_obj;
lean_object* v___y_2075_ = stack[4].m_obj;
lean_object* v___y_2076_ = stack[5].m_obj;
lean_object* v___y_2077_ = stack[6].m_obj;
lean_object* v___y_2078_ = stack[7].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_mvarId_2071_, v_idx_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
stack->m_obj
 = v_res_2155_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___boxed(lean_object* v_mvarId_2156_, lean_object* v_idx_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_mvarId_2156_, v_idx_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2165_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC(lean_object* v_goal_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v_initialCtxSize_2174_; lean_object* v___x_2175_; 
v_initialCtxSize_2174_ = lean_ctor_get(v_a_2167_, 5);
lean_inc(v_initialCtxSize_2174_);
lean_inc(v_goal_2166_);
v___x_2175_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_goal_2166_, v_initialCtxSize_2174_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v___x_2176_; 
lean_dec_ref_known(v___x_2175_, 1);
lean_inc(v_goal_2166_);
v___x_2176_ = l_Lean_MVarId_getType(v_goal_2166_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = 2;
lean_inc(v_goal_2166_);
v___x_2179_ = l_Lean_MVarId_setKind___redArg(v_goal_2166_, v___x_2178_, v_a_2170_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2222_; 
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v___x_2179_, 0);
lean_dec(v_unused_2223_);
v___x_2181_ = v___x_2179_;
v_isShared_2182_ = v_isSharedCheck_2222_;
goto v_resetjp_2180_;
}
else
{
lean_dec(v___x_2179_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2222_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v_env_2184_; uint8_t v___x_2185_; 
v___x_2183_ = lean_st_ref_get(v_a_2172_);
v_env_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc_ref(v_env_2184_);
lean_dec(v___x_2183_);
v___x_2185_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_2184_, v_a_2177_);
lean_dec(v_a_2177_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v_fuel_2187_; lean_object* v_simpState_2188_; lean_object* v_invariants_2189_; lean_object* v_vcs_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2203_; 
v___x_2186_ = lean_st_ref_take(v_a_2168_);
v_fuel_2187_ = lean_ctor_get(v___x_2186_, 0);
v_simpState_2188_ = lean_ctor_get(v___x_2186_, 1);
v_invariants_2189_ = lean_ctor_get(v___x_2186_, 2);
v_vcs_2190_ = lean_ctor_get(v___x_2186_, 3);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2192_ = v___x_2186_;
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_vcs_2190_);
lean_inc(v_invariants_2189_);
lean_inc(v_simpState_2188_);
lean_inc(v_fuel_2187_);
lean_dec(v___x_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_array_push(v_vcs_2190_, v_goal_2166_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 3, v___x_2195_);
v___x_2197_ = v___x_2192_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_fuel_2187_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_simpState_2188_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_invariants_2189_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_st_ref_put(v_a_2168_, v___x_2197_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2194_);
v___x_2200_ = v___x_2181_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2194_);
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
else
{
lean_object* v___x_2204_; lean_object* v_fuel_2205_; lean_object* v_simpState_2206_; lean_object* v_invariants_2207_; lean_object* v_vcs_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2221_; 
v___x_2204_ = lean_st_ref_take(v_a_2168_);
v_fuel_2205_ = lean_ctor_get(v___x_2204_, 0);
v_simpState_2206_ = lean_ctor_get(v___x_2204_, 1);
v_invariants_2207_ = lean_ctor_get(v___x_2204_, 2);
v_vcs_2208_ = lean_ctor_get(v___x_2204_, 3);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2210_ = v___x_2204_;
v_isShared_2211_ = v_isSharedCheck_2221_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_vcs_2208_);
lean_inc(v_invariants_2207_);
lean_inc(v_simpState_2206_);
lean_inc(v_fuel_2205_);
lean_dec(v___x_2204_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2221_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_array_push(v_invariants_2207_, v_goal_2166_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 2, v___x_2213_);
v___x_2215_ = v___x_2210_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_fuel_2205_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_simpState_2206_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v_vcs_2208_);
v___x_2215_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = lean_st_ref_put(v_a_2168_, v___x_2215_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2212_);
v___x_2218_ = v___x_2181_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2212_);
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
}
else
{
lean_dec(v_a_2177_);
lean_dec(v_goal_2166_);
return v___x_2179_;
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_goal_2166_);
v_a_2224_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2176_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2176_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_dec(v_goal_2166_);
return v___x_2175_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_addSubGoalAsVC_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2166_ = stack[0].m_obj;
lean_object* v_a_2167_ = stack[1].m_obj;
lean_object* v_a_2168_ = stack[2].m_obj;
lean_object* v_a_2169_ = stack[3].m_obj;
lean_object* v_a_2170_ = stack[4].m_obj;
lean_object* v_a_2171_ = stack[5].m_obj;
lean_object* v_a_2172_ = stack[6].m_obj;
lean_object* v_res_2232_;
v_res_2232_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v_goal_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
stack->m_obj
 = v_res_2232_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC___boxed(lean_object* v_goal_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v_goal_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1(lean_object* v_00_u03b2_2242_, lean_object* v_x_2243_, lean_object* v_x_2244_, lean_object* v_x_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_x_2243_, v_x_2244_, v_x_2245_);
return v___x_2246_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(lean_object* v_range_2247_, lean_object* v_b_2248_, lean_object* v_i_2249_, lean_object* v_hs_2250_, lean_object* v_hl_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_2247_, v_b_2248_, v_i_2249_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_2247_ = stack[0].m_obj;
lean_object* v_b_2248_ = stack[1].m_obj;
lean_object* v_i_2249_ = stack[2].m_obj;
lean_object* v___y_2252_ = stack[5].m_obj;
lean_object* v___y_2253_ = stack[6].m_obj;
lean_object* v___y_2254_ = stack[7].m_obj;
lean_object* v___y_2255_ = stack[8].m_obj;
lean_object* v___y_2256_ = stack[9].m_obj;
lean_object* v___y_2257_ = stack[10].m_obj;
lean_object* v_res_2260_;
v_res_2260_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(v_range_2247_, v_b_2248_, v_i_2249_, lean_box(0), lean_box(0), v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
stack->m_obj
 = v_res_2260_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___boxed(lean_object* v_range_2261_, lean_object* v_b_2262_, lean_object* v_i_2263_, lean_object* v_hs_2264_, lean_object* v_hl_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(v_range_2261_, v_b_2262_, v_i_2263_, v_hs_2264_, v_hl_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v_range_2261_);
return v_res_2273_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2274_, lean_object* v_x_2275_, size_t v_x_2276_, size_t v_x_2277_, lean_object* v_x_2278_, lean_object* v_x_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_2275_, v_x_2276_, v_x_2277_, v_x_2278_, v_x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2275_ = stack[1].m_obj;
size_t v_x_2276_ = stack[2].m_num;
size_t v_x_2277_ = stack[3].m_num;
lean_object* v_x_2278_ = stack[4].m_obj;
lean_object* v_x_2279_ = stack[5].m_obj;
lean_object* v_res_2281_;
v_res_2281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(lean_box(0), v_x_2275_, v_x_2276_, v_x_2277_, v_x_2278_, v_x_2279_);
stack->m_obj
 = v_res_2281_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
size_t v_x_8019__boxed_2288_; size_t v_x_8020__boxed_2289_; lean_object* v_res_2290_; 
v_x_8019__boxed_2288_ = lean_unbox_usize(v_x_2284_);
lean_dec(v_x_2284_);
v_x_8020__boxed_2289_ = lean_unbox_usize(v_x_2285_);
lean_dec(v_x_2285_);
v_res_2290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(v_00_u03b2_2282_, v_x_2283_, v_x_8019__boxed_2288_, v_x_8020__boxed_2289_, v_x_2286_, v_x_2287_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2291_, lean_object* v_n_2292_, lean_object* v_k_2293_, lean_object* v_v_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v_n_2292_, v_k_2293_, v_v_2294_);
return v___x_2295_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2296_, size_t v_depth_2297_, lean_object* v_keys_2298_, lean_object* v_vals_2299_, lean_object* v_heq_2300_, lean_object* v_i_2301_, lean_object* v_entries_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_2297_, v_keys_2298_, v_vals_2299_, v_i_2301_, v_entries_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2297_ = stack[1].m_num;
lean_object* v_keys_2298_ = stack[2].m_obj;
lean_object* v_vals_2299_ = stack[3].m_obj;
lean_object* v_i_2301_ = stack[5].m_obj;
lean_object* v_entries_2302_ = stack[6].m_obj;
lean_object* v_res_2304_;
v_res_2304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(lean_box(0), v_depth_2297_, v_keys_2298_, v_vals_2299_, lean_box(0), v_i_2301_, v_entries_2302_);
stack->m_obj
 = v_res_2304_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2305_, lean_object* v_depth_2306_, lean_object* v_keys_2307_, lean_object* v_vals_2308_, lean_object* v_heq_2309_, lean_object* v_i_2310_, lean_object* v_entries_2311_){
_start:
{
size_t v_depth_boxed_2312_; lean_object* v_res_2313_; 
v_depth_boxed_2312_ = lean_unbox_usize(v_depth_2306_);
lean_dec(v_depth_2306_);
v_res_2313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(v_00_u03b2_2305_, v_depth_boxed_2312_, v_keys_2307_, v_vals_2308_, v_heq_2309_, v_i_2310_, v_entries_2311_);
lean_dec_ref(v_vals_2308_);
lean_dec_ref(v_keys_2307_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2315_, v_x_2316_, v_x_2317_, v_x_2318_);
return v___x_2319_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_emitVC(lean_object* v_subGoal_2320_, lean_object* v_name_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_subGoal_2320_, v_name_2321_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = l_Lean_Expr_mvarId_x21(v_a_2330_);
v___x_2332_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v___x_2331_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v___x_2332_, 0);
lean_dec(v_unused_2340_);
v___x_2334_ = v___x_2332_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_dec(v___x_2332_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v_a_2330_);
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2330_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2330_);
v_a_2341_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2332_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2332_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
return v___x_2329_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_emitVC_0interp(lean_interpreter_value* stack)
{
lean_object* v_subGoal_2320_ = stack[0].m_obj;
lean_object* v_name_2321_ = stack[1].m_obj;
lean_object* v_a_2322_ = stack[2].m_obj;
lean_object* v_a_2323_ = stack[3].m_obj;
lean_object* v_a_2324_ = stack[4].m_obj;
lean_object* v_a_2325_ = stack[5].m_obj;
lean_object* v_a_2326_ = stack[6].m_obj;
lean_object* v_a_2327_ = stack[7].m_obj;
lean_object* v_res_2349_;
v_res_2349_ = l_Lean_Elab_Tactic_Do_emitVC(v_subGoal_2320_, v_name_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
stack->m_obj
 = v_res_2349_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC___boxed(lean_object* v_subGoal_2350_, lean_object* v_name_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_Elab_Tactic_Do_emitVC(v_subGoal_2350_, v_name_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
return v_res_2359_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg(lean_object* v_x_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v___x_2368_; lean_object* v_simpCtx_2369_; lean_object* v_simprocs_2370_; lean_object* v_fuel_2371_; lean_object* v_simpState_2372_; lean_object* v_invariants_2373_; lean_object* v_vcs_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2395_; 
v___x_2368_ = lean_st_ref_get(v_a_2362_);
v_simpCtx_2369_ = lean_ctor_get(v_a_2361_, 2);
v_simprocs_2370_ = lean_ctor_get(v_a_2361_, 3);
v_fuel_2371_ = lean_ctor_get(v___x_2368_, 0);
v_simpState_2372_ = lean_ctor_get(v___x_2368_, 1);
v_invariants_2373_ = lean_ctor_get(v___x_2368_, 2);
v_vcs_2374_ = lean_ctor_get(v___x_2368_, 3);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2376_ = v___x_2368_;
v_isShared_2377_ = v_isSharedCheck_2395_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_vcs_2374_);
lean_inc(v_invariants_2373_);
lean_inc(v_simpState_2372_);
lean_inc(v_fuel_2371_);
lean_dec(v___x_2368_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2395_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_inc_ref(v_simprocs_2370_);
v___x_2378_ = l_Lean_Meta_Simp_mkDefaultMethodsCore(v_simprocs_2370_);
v___x_2379_ = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(v___x_2378_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = lean_st_mk_ref(v_simpState_2372_);
lean_inc(v_a_2366_);
lean_inc_ref(v_a_2365_);
lean_inc(v_a_2364_);
lean_inc_ref(v_a_2363_);
lean_inc(v___x_2380_);
lean_inc_ref(v_simpCtx_2369_);
v___x_2381_ = lean_apply_8(v_x_2360_, v___x_2379_, v_simpCtx_2369_, v___x_2380_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, lean_box(0));
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2394_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2394_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2394_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_st_ref_get(v___x_2380_);
lean_dec(v___x_2380_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v___x_2386_);
v___x_2388_ = v___x_2376_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_fuel_2371_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_invariants_2373_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_vcs_2374_);
v___x_2388_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_st_ref_swap(v_a_2362_, v___x_2388_);
lean_dec(v___x_2389_);
if (v_isShared_2385_ == 0)
{
v___x_2391_ = v___x_2384_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2382_);
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
else
{
lean_dec(v___x_2380_);
lean_del_object(v___x_2376_);
lean_dec_ref(v_vcs_2374_);
lean_dec_ref(v_invariants_2373_);
lean_dec(v_fuel_2371_);
return v___x_2381_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_liftSimpM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2360_ = stack[0].m_obj;
lean_object* v_a_2361_ = stack[1].m_obj;
lean_object* v_a_2362_ = stack[2].m_obj;
lean_object* v_a_2363_ = stack[3].m_obj;
lean_object* v_a_2364_ = stack[4].m_obj;
lean_object* v_a_2365_ = stack[5].m_obj;
lean_object* v_a_2366_ = stack[6].m_obj;
lean_object* v_res_2396_;
v_res_2396_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
stack->m_obj
 = v_res_2396_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg___boxed(lean_object* v_x_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
return v_res_2405_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_liftSimpM(lean_object* v_00_u03b1_2406_, lean_object* v_x_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2415_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_liftSimpM_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2407_ = stack[1].m_obj;
lean_object* v_a_2408_ = stack[2].m_obj;
lean_object* v_a_2409_ = stack[3].m_obj;
lean_object* v_a_2410_ = stack[4].m_obj;
lean_object* v_a_2411_ = stack[5].m_obj;
lean_object* v_a_2412_ = stack[6].m_obj;
lean_object* v_a_2413_ = stack[7].m_obj;
lean_object* v_res_2416_;
v_res_2416_ = l_Lean_Elab_Tactic_Do_liftSimpM(lean_box(0), v_x_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
stack->m_obj
 = v_res_2416_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___boxed(lean_object* v_00_u03b1_2417_, lean_object* v_x_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_Elab_Tactic_Do_liftSimpM(v_00_u03b1_2417_, v_x_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
return v_res_2426_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(lean_object* v_00_u03b1_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2428_ = stack[1].m_obj;
lean_object* v___y_2429_ = stack[2].m_obj;
lean_object* v___y_2430_ = stack[3].m_obj;
lean_object* v___y_2431_ = stack[4].m_obj;
lean_object* v___y_2432_ = stack[5].m_obj;
lean_object* v___y_2433_ = stack[6].m_obj;
lean_object* v___y_2434_ = stack[7].m_obj;
lean_object* v_res_2437_;
v_res_2437_ = l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(lean_box(0), v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
stack->m_obj
 = v_res_2437_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0___boxed(lean_object* v_00_u03b1_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(v_00_u03b1_2438_, v_x_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2447_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg(lean_object* v_jp_2450_, lean_object* v_info_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_config_2460_; lean_object* v_specThms_2461_; lean_object* v_simpCtx_2462_; lean_object* v_simprocs_2463_; lean_object* v_jps_2464_; lean_object* v_initialCtxSize_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_config_2460_ = lean_ctor_get(v_a_2453_, 0);
v_specThms_2461_ = lean_ctor_get(v_a_2453_, 1);
v_simpCtx_2462_ = lean_ctor_get(v_a_2453_, 2);
v_simprocs_2463_ = lean_ctor_get(v_a_2453_, 3);
v_jps_2464_ = lean_ctor_get(v_a_2453_, 4);
v_initialCtxSize_2465_ = lean_ctor_get(v_a_2453_, 5);
lean_inc(v_jps_2464_);
v___x_2466_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_jp_2450_, v_info_2451_, v_jps_2464_);
lean_inc(v_initialCtxSize_2465_);
lean_inc_ref(v_simprocs_2463_);
lean_inc_ref(v_simpCtx_2462_);
lean_inc_ref(v_specThms_2461_);
lean_inc_ref(v_config_2460_);
v___x_2467_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2467_, 0, v_config_2460_);
lean_ctor_set(v___x_2467_, 1, v_specThms_2461_);
lean_ctor_set(v___x_2467_, 2, v_simpCtx_2462_);
lean_ctor_set(v___x_2467_, 3, v_simprocs_2463_);
lean_ctor_set(v___x_2467_, 4, v___x_2466_);
lean_ctor_set(v___x_2467_, 5, v_initialCtxSize_2465_);
lean_inc(v_a_2458_);
lean_inc_ref(v_a_2457_);
lean_inc(v_a_2456_);
lean_inc_ref(v_a_2455_);
lean_inc(v_a_2454_);
v___x_2468_ = lean_apply_7(v_a_2452_, v___x_2467_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, lean_box(0));
return v___x_2468_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withJP___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jp_2450_ = stack[0].m_obj;
lean_object* v_info_2451_ = stack[1].m_obj;
lean_object* v_a_2452_ = stack[2].m_obj;
lean_object* v_a_2453_ = stack[3].m_obj;
lean_object* v_a_2454_ = stack[4].m_obj;
lean_object* v_a_2455_ = stack[5].m_obj;
lean_object* v_a_2456_ = stack[6].m_obj;
lean_object* v_a_2457_ = stack[7].m_obj;
lean_object* v_a_2458_ = stack[8].m_obj;
lean_object* v_res_2469_;
v_res_2469_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_2450_, v_info_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
stack->m_obj
 = v_res_2469_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg___boxed(lean_object* v_jp_2470_, lean_object* v_info_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_2470_, v_info_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2480_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withJP(lean_object* v_00_u03b1_2481_, lean_object* v_jp_2482_, lean_object* v_info_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_2482_, v_info_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withJP_0interp(lean_interpreter_value* stack)
{
lean_object* v_jp_2482_ = stack[1].m_obj;
lean_object* v_info_2483_ = stack[2].m_obj;
lean_object* v_a_2484_ = stack[3].m_obj;
lean_object* v_a_2485_ = stack[4].m_obj;
lean_object* v_a_2486_ = stack[5].m_obj;
lean_object* v_a_2487_ = stack[6].m_obj;
lean_object* v_a_2488_ = stack[7].m_obj;
lean_object* v_a_2489_ = stack[8].m_obj;
lean_object* v_a_2490_ = stack[9].m_obj;
lean_object* v_res_2493_;
v_res_2493_ = l_Lean_Elab_Tactic_Do_withJP(lean_box(0), v_jp_2482_, v_info_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
stack->m_obj
 = v_res_2493_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_jp_2495_, lean_object* v_info_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Elab_Tactic_Do_withJP(v_00_u03b1_2494_, v_jp_2495_, v_info_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(lean_object* v_t_2506_, lean_object* v_k_2507_){
_start:
{
if (lean_obj_tag(v_t_2506_) == 0)
{
lean_object* v_k_2508_; lean_object* v_v_2509_; lean_object* v_l_2510_; lean_object* v_r_2511_; uint8_t v___x_2512_; 
v_k_2508_ = lean_ctor_get(v_t_2506_, 1);
v_v_2509_ = lean_ctor_get(v_t_2506_, 2);
v_l_2510_ = lean_ctor_get(v_t_2506_, 3);
v_r_2511_ = lean_ctor_get(v_t_2506_, 4);
v___x_2512_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2507_, v_k_2508_);
switch(v___x_2512_)
{
case 0:
{
v_t_2506_ = v_l_2510_;
goto _start;
}
case 1:
{
lean_object* v___x_2514_; 
lean_inc(v_v_2509_);
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_v_2509_);
return v___x_2514_;
}
default: 
{
v_t_2506_ = v_r_2511_;
goto _start;
}
}
}
else
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_box(0);
return v___x_2516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_2517_, lean_object* v_k_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_2517_, v_k_2518_);
lean_dec(v_k_2518_);
lean_dec(v_t_2517_);
return v_res_2519_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(lean_object* v_jp_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_jps_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_jps_2523_ = lean_ctor_get(v_a_2521_, 4);
v___x_2524_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_jps_2523_, v_jp_2520_);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jp_2520_ = stack[0].m_obj;
lean_object* v_a_2521_ = stack[1].m_obj;
lean_object* v_res_2526_;
v_res_2526_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_2520_, v_a_2521_);
stack->m_obj
 = v_res_2526_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg___boxed(lean_object* v_jp_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_2527_, v_a_2528_);
lean_dec_ref(v_a_2528_);
lean_dec(v_jp_2527_);
return v_res_2530_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f(lean_object* v_jp_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_2531_, v_a_2532_);
return v___x_2539_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_knownJP_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_jp_2531_ = stack[0].m_obj;
lean_object* v_a_2532_ = stack[1].m_obj;
lean_object* v_a_2533_ = stack[2].m_obj;
lean_object* v_a_2534_ = stack[3].m_obj;
lean_object* v_a_2535_ = stack[4].m_obj;
lean_object* v_a_2536_ = stack[5].m_obj;
lean_object* v_a_2537_ = stack[6].m_obj;
lean_object* v_res_2540_;
v_res_2540_ = l_Lean_Elab_Tactic_Do_knownJP_x3f(v_jp_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
stack->m_obj
 = v_res_2540_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___boxed(lean_object* v_jp_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_Elab_Tactic_Do_knownJP_x3f(v_jp_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_jp_2541_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(lean_object* v_00_u03b4_2550_, lean_object* v_t_2551_, lean_object* v_k_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_2551_, v_k_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_2554_, lean_object* v_t_2555_, lean_object* v_k_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(v_00_u03b4_2554_, v_t_2555_, v_k_2556_);
lean_dec(v_k_2556_);
lean_dec(v_t_2555_);
return v_res_2557_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_isDuplicable(lean_object* v_e_2563_){
_start:
{
switch(lean_obj_tag(v_e_2563_))
{
case 5:
{
lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isDuplicable___closed__2));
v___x_2565_ = l_Lean_Expr_isAppOf(v_e_2563_, v___x_2564_);
return v___x_2565_;
}
case 6:
{
uint8_t v___x_2566_; 
v___x_2566_ = 0;
return v___x_2566_;
}
case 7:
{
uint8_t v___x_2567_; 
v___x_2567_ = 0;
return v___x_2567_;
}
case 8:
{
uint8_t v___x_2568_; 
v___x_2568_ = 0;
return v___x_2568_;
}
case 10:
{
lean_object* v_expr_2569_; 
v_expr_2569_ = lean_ctor_get(v_e_2563_, 1);
v_e_2563_ = v_expr_2569_;
goto _start;
}
case 11:
{
lean_object* v_struct_2571_; 
v_struct_2571_ = lean_ctor_get(v_e_2563_, 2);
v_e_2563_ = v_struct_2571_;
goto _start;
}
default: 
{
uint8_t v___x_2573_; 
v___x_2573_ = 1;
return v___x_2573_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_isDuplicable_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2563_ = stack[0].m_obj;
uint8_t v_res_2574_;
v_res_2574_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_e_2563_);
stack->m_num = v_res_2574_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___boxed(lean_object* v_e_2575_){
_start:
{
uint8_t v_res_2576_; lean_object* v_r_2577_; 
v_res_2576_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_e_2575_);
lean_dec_ref(v_e_2575_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(lean_object* v_k_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
lean_inc(v___y_2585_);
lean_inc_ref(v___y_2584_);
lean_inc(v___y_2583_);
lean_inc_ref(v___y_2582_);
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
v___x_2587_ = lean_apply_8(v_k_2578_, v_b_2581_, v___y_2579_, v___y_2580_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, lean_box(0));
return v___x_2587_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2578_ = stack[0].m_obj;
lean_object* v___y_2579_ = stack[1].m_obj;
lean_object* v___y_2580_ = stack[2].m_obj;
lean_object* v_b_2581_ = stack[3].m_obj;
lean_object* v___y_2582_ = stack[4].m_obj;
lean_object* v___y_2583_ = stack[5].m_obj;
lean_object* v___y_2584_ = stack[6].m_obj;
lean_object* v___y_2585_ = stack[7].m_obj;
lean_object* v_res_2588_;
v_res_2588_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(v_k_2578_, v___y_2579_, v___y_2580_, v_b_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
stack->m_obj
 = v_res_2588_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed(lean_object* v_k_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(v_k_2589_, v___y_2590_, v___y_2591_, v_b_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2598_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(lean_object* v_name_2599_, lean_object* v_type_2600_, lean_object* v_val_2601_, lean_object* v_k_2602_, uint8_t v_nondep_2603_, uint8_t v_kind_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___f_2612_; lean_object* v___x_2613_; 
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
v___f_2612_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2612_, 0, v_k_2602_);
lean_closure_set(v___f_2612_, 1, v___y_2605_);
lean_closure_set(v___f_2612_, 2, v___y_2606_);
v___x_2613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2599_, v_type_2600_, v_val_2601_, v___f_2612_, v_nondep_2603_, v_kind_2604_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2613_) == 0)
{
return v___x_2613_;
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2599_ = stack[0].m_obj;
lean_object* v_type_2600_ = stack[1].m_obj;
lean_object* v_val_2601_ = stack[2].m_obj;
lean_object* v_k_2602_ = stack[3].m_obj;
uint8_t v_nondep_2603_ = stack[4].m_num;
uint8_t v_kind_2604_ = stack[5].m_num;
lean_object* v___y_2605_ = stack[6].m_obj;
lean_object* v___y_2606_ = stack[7].m_obj;
lean_object* v___y_2607_ = stack[8].m_obj;
lean_object* v___y_2608_ = stack[9].m_obj;
lean_object* v___y_2609_ = stack[10].m_obj;
lean_object* v___y_2610_ = stack[11].m_obj;
lean_object* v_res_2622_;
v_res_2622_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2599_, v_type_2600_, v_val_2601_, v_k_2602_, v_nondep_2603_, v_kind_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
stack->m_obj
 = v_res_2622_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___boxed(lean_object* v_name_2623_, lean_object* v_type_2624_, lean_object* v_val_2625_, lean_object* v_k_2626_, lean_object* v_nondep_2627_, lean_object* v_kind_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v_nondep_boxed_2636_; uint8_t v_kind_boxed_2637_; lean_object* v_res_2638_; 
v_nondep_boxed_2636_ = lean_unbox(v_nondep_2627_);
v_kind_boxed_2637_ = lean_unbox(v_kind_2628_);
v_res_2638_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2623_, v_type_2624_, v_val_2625_, v_k_2626_, v_nondep_boxed_2636_, v_kind_boxed_2637_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
return v_res_2638_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(lean_object* v_00_u03b1_2639_, lean_object* v_name_2640_, lean_object* v_type_2641_, lean_object* v_val_2642_, lean_object* v_k_2643_, uint8_t v_nondep_2644_, uint8_t v_kind_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2640_, v_type_2641_, v_val_2642_, v_k_2643_, v_nondep_2644_, v_kind_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2640_ = stack[1].m_obj;
lean_object* v_type_2641_ = stack[2].m_obj;
lean_object* v_val_2642_ = stack[3].m_obj;
lean_object* v_k_2643_ = stack[4].m_obj;
uint8_t v_nondep_2644_ = stack[5].m_num;
uint8_t v_kind_2645_ = stack[6].m_num;
lean_object* v___y_2646_ = stack[7].m_obj;
lean_object* v___y_2647_ = stack[8].m_obj;
lean_object* v___y_2648_ = stack[9].m_obj;
lean_object* v___y_2649_ = stack[10].m_obj;
lean_object* v___y_2650_ = stack[11].m_obj;
lean_object* v___y_2651_ = stack[12].m_obj;
lean_object* v_res_2654_;
v_res_2654_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(lean_box(0), v_name_2640_, v_type_2641_, v_val_2642_, v_k_2643_, v_nondep_2644_, v_kind_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
stack->m_obj
 = v_res_2654_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___boxed(lean_object* v_00_u03b1_2655_, lean_object* v_name_2656_, lean_object* v_type_2657_, lean_object* v_val_2658_, lean_object* v_k_2659_, lean_object* v_nondep_2660_, lean_object* v_kind_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v_nondep_boxed_2669_; uint8_t v_kind_boxed_2670_; lean_object* v_res_2671_; 
v_nondep_boxed_2669_ = lean_unbox(v_nondep_2660_);
v_kind_boxed_2670_ = lean_unbox(v_kind_2661_);
v_res_2671_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(v_00_u03b1_2655_, v_name_2656_, v_type_2657_, v_val_2658_, v_k_2659_, v_nondep_boxed_2669_, v_kind_boxed_2670_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2671_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(lean_object* v___x_2672_, lean_object* v_x_2673_, uint8_t v___x_2674_, uint8_t v___x_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_Meta_mkLetFVars(v___x_2672_, v_x_2673_, v___x_2674_, v___x_2674_, v___x_2675_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2672_ = stack[0].m_obj;
lean_object* v_x_2673_ = stack[1].m_obj;
uint8_t v___x_2674_ = stack[2].m_num;
uint8_t v___x_2675_ = stack[3].m_num;
lean_object* v___y_2676_ = stack[4].m_obj;
lean_object* v___y_2677_ = stack[5].m_obj;
lean_object* v___y_2678_ = stack[6].m_obj;
lean_object* v___y_2679_ = stack[7].m_obj;
lean_object* v___y_2680_ = stack[8].m_obj;
lean_object* v___y_2681_ = stack[9].m_obj;
lean_object* v___y_2682_ = stack[10].m_obj;
lean_object* v_res_2685_;
v_res_2685_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(v___x_2672_, v_x_2673_, v___x_2674_, v___x_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
stack->m_obj
 = v_res_2685_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed(lean_object* v___x_2686_, lean_object* v_x_2687_, lean_object* v___x_2688_, lean_object* v___x_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v___x_1489__boxed_2698_; uint8_t v___x_1490__boxed_2699_; lean_object* v_res_2700_; 
v___x_1489__boxed_2698_ = lean_unbox(v___x_2688_);
v___x_1490__boxed_2699_ = lean_unbox(v___x_2689_);
v_res_2700_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(v___x_2686_, v_x_2687_, v___x_1489__boxed_2698_, v___x_1490__boxed_2699_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___x_2686_);
return v_res_2700_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(lean_object* v_fv_2701_, uint8_t v___x_2702_, lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___f_2717_; lean_object* v___x_2718_; 
v___x_2711_ = lean_unsigned_to_nat(1u);
v___x_2712_ = lean_mk_empty_array_with_capacity(v___x_2711_);
v___x_2713_ = lean_array_push(v___x_2712_, v_fv_2701_);
v___x_2714_ = 1;
v___x_2715_ = lean_box(v___x_2702_);
v___x_2716_ = lean_box(v___x_2714_);
v___f_2717_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_2717_, 0, v___x_2713_);
lean_closure_set(v___f_2717_, 1, v_x_2703_);
lean_closure_set(v___f_2717_, 2, v___x_2715_);
lean_closure_set(v___f_2717_, 3, v___x_2716_);
v___x_2718_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_2717_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2718_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fv_2701_ = stack[0].m_obj;
uint8_t v___x_2702_ = stack[1].m_num;
lean_object* v_x_2703_ = stack[2].m_obj;
lean_object* v___y_2704_ = stack[3].m_obj;
lean_object* v___y_2705_ = stack[4].m_obj;
lean_object* v___y_2706_ = stack[5].m_obj;
lean_object* v___y_2707_ = stack[6].m_obj;
lean_object* v___y_2708_ = stack[7].m_obj;
lean_object* v___y_2709_ = stack[8].m_obj;
lean_object* v_res_2719_;
v_res_2719_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(v_fv_2701_, v___x_2702_, v_x_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
stack->m_obj
 = v_res_2719_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed(lean_object* v_fv_2720_, lean_object* v___x_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
uint8_t v___x_1550__boxed_2730_; lean_object* v_res_2731_; 
v___x_1550__boxed_2730_ = lean_unbox(v___x_2721_);
v_res_2731_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(v_fv_2720_, v___x_1550__boxed_2730_, v_x_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2731_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(uint8_t v___x_2732_, lean_object* v_k_2733_, lean_object* v_fv_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; lean_object* v___f_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2742_ = lean_box(v___x_2732_);
lean_inc_ref(v_fv_2734_);
v___f_2743_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2743_, 0, v_fv_2734_);
lean_closure_set(v___f_2743_, 1, v___x_2742_);
v___x_2744_ = lean_box(v___x_2732_);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2739_);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
v___x_2745_ = lean_apply_10(v_k_2733_, v___x_2744_, v_fv_2734_, v___f_2743_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, lean_box(0));
return v___x_2745_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2732_ = stack[0].m_num;
lean_object* v_k_2733_ = stack[1].m_obj;
lean_object* v_fv_2734_ = stack[2].m_obj;
lean_object* v___y_2735_ = stack[3].m_obj;
lean_object* v___y_2736_ = stack[4].m_obj;
lean_object* v___y_2737_ = stack[5].m_obj;
lean_object* v___y_2738_ = stack[6].m_obj;
lean_object* v___y_2739_ = stack[7].m_obj;
lean_object* v___y_2740_ = stack[8].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(v___x_2732_, v_k_2733_, v_fv_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
stack->m_obj
 = v_res_2746_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed(lean_object* v___x_2747_, lean_object* v_k_2748_, lean_object* v_fv_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
uint8_t v___x_1619__boxed_2757_; lean_object* v_res_2758_; 
v___x_1619__boxed_2757_ = lean_unbox(v___x_2747_);
v_res_2758_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(v___x_1619__boxed_2757_, v_k_2748_, v_fv_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2758_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___y_2759_);
return v___x_2767_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2759_ = stack[0].m_obj;
lean_object* v___y_2760_ = stack[1].m_obj;
lean_object* v___y_2761_ = stack[2].m_obj;
lean_object* v___y_2762_ = stack[3].m_obj;
lean_object* v___y_2763_ = stack[4].m_obj;
lean_object* v___y_2764_ = stack[5].m_obj;
lean_object* v___y_2765_ = stack[6].m_obj;
lean_object* v_res_2768_;
v_res_2768_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
stack->m_obj
 = v_res_2768_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3___boxed(lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2777_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(lean_object* v_name_2779_, lean_object* v_type_2780_, lean_object* v_val_2781_, lean_object* v_k_2782_, uint8_t v_kind_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_val_2781_);
if (v___x_2791_ == 0)
{
uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; 
v___x_2792_ = 1;
v___x_2793_ = lean_box(v___x_2792_);
v___f_2794_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed), 10, 2);
lean_closure_set(v___f_2794_, 0, v___x_2793_);
lean_closure_set(v___f_2794_, 1, v_k_2782_);
v___x_2795_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2779_, v_type_2780_, v_val_2781_, v___f_2794_, v___x_2791_, v_kind_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
return v___x_2795_;
}
else
{
lean_object* v___f_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec_ref(v_type_2780_);
lean_dec(v_name_2779_);
v___f_2796_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___closed__0));
v___x_2797_ = 0;
v___x_2798_ = lean_box(v___x_2797_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc(v_a_2787_);
lean_inc_ref(v_a_2786_);
lean_inc(v_a_2785_);
lean_inc_ref(v_a_2784_);
v___x_2799_ = lean_apply_10(v_k_2782_, v___x_2798_, v_val_2781_, v___f_2796_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, lean_box(0));
return v___x_2799_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2779_ = stack[0].m_obj;
lean_object* v_type_2780_ = stack[1].m_obj;
lean_object* v_val_2781_ = stack[2].m_obj;
lean_object* v_k_2782_ = stack[3].m_obj;
uint8_t v_kind_2783_ = stack[4].m_num;
lean_object* v_a_2784_ = stack[5].m_obj;
lean_object* v_a_2785_ = stack[6].m_obj;
lean_object* v_a_2786_ = stack[7].m_obj;
lean_object* v_a_2787_ = stack[8].m_obj;
lean_object* v_a_2788_ = stack[9].m_obj;
lean_object* v_a_2789_ = stack[10].m_obj;
lean_object* v_res_2800_;
v_res_2800_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2779_, v_type_2780_, v_val_2781_, v_k_2782_, v_kind_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___boxed(lean_object* v_name_2801_, lean_object* v_type_2802_, lean_object* v_val_2803_, lean_object* v_k_2804_, lean_object* v_kind_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v_kind_boxed_2813_; lean_object* v_res_2814_; 
v_kind_boxed_2813_ = lean_unbox(v_kind_2805_);
v_res_2814_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2801_, v_type_2802_, v_val_2803_, v_k_2804_, v_kind_boxed_2813_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
return v_res_2814_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared(lean_object* v_00_u03b1_2815_, lean_object* v_name_2816_, lean_object* v_type_2817_, lean_object* v_val_2818_, lean_object* v_k_2819_, uint8_t v_kind_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2816_, v_type_2817_, v_val_2818_, v_k_2819_, v_kind_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withLetDeclShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2816_ = stack[1].m_obj;
lean_object* v_type_2817_ = stack[2].m_obj;
lean_object* v_val_2818_ = stack[3].m_obj;
lean_object* v_k_2819_ = stack[4].m_obj;
uint8_t v_kind_2820_ = stack[5].m_num;
lean_object* v_a_2821_ = stack[6].m_obj;
lean_object* v_a_2822_ = stack[7].m_obj;
lean_object* v_a_2823_ = stack[8].m_obj;
lean_object* v_a_2824_ = stack[9].m_obj;
lean_object* v_a_2825_ = stack[10].m_obj;
lean_object* v_a_2826_ = stack[11].m_obj;
lean_object* v_res_2829_;
v_res_2829_ = l_Lean_Elab_Tactic_Do_withLetDeclShared(lean_box(0), v_name_2816_, v_type_2817_, v_val_2818_, v_k_2819_, v_kind_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
stack->m_obj
 = v_res_2829_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_name_2831_, lean_object* v_type_2832_, lean_object* v_val_2833_, lean_object* v_k_2834_, lean_object* v_kind_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
uint8_t v_kind_boxed_2843_; lean_object* v_res_2844_; 
v_kind_boxed_2843_ = lean_unbox(v_kind_2835_);
v_res_2844_ = l_Lean_Elab_Tactic_Do_withLetDeclShared(v_00_u03b1_2830_, v_name_2831_, v_type_2832_, v_val_2833_, v_k_2834_, v_kind_boxed_2843_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
return v_res_2844_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object* v_n_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2849_ = l_Lean_Name_eraseMacroScopes(v_n_2848_);
v___x_2850_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isJP___closed__1));
v___x_2851_ = lean_name_eq(v___x_2849_, v___x_2850_);
lean_dec(v___x_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_isJP_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2848_ = stack[0].m_obj;
uint8_t v_res_2852_;
v_res_2852_ = l_Lean_Elab_Tactic_Do_isJP(v_n_2848_);
stack->m_num = v_res_2852_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isJP___boxed(lean_object* v_n_2853_){
_start:
{
uint8_t v_res_2854_; lean_object* v_r_2855_; 
v_res_2854_ = l_Lean_Elab_Tactic_Do_isJP(v_n_2853_);
lean_dec(v_n_2853_);
v_r_2855_ = lean_box(v_res_2854_);
return v_r_2855_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__0));
v___x_2858_ = l_Lean_stringToMessageData(v___x_2857_);
return v___x_2858_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams(lean_object* v_joinTy_2859_, lean_object* v_resTy_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = l_Lean_Expr_isMData(v_joinTy_2859_);
if (v___x_2866_ == 0)
{
uint8_t v___x_2867_; 
v___x_2867_ = lean_expr_eqv(v_joinTy_2859_, v_resTy_2860_);
if (v___x_2867_ == 0)
{
uint8_t v___x_2868_; 
v___x_2868_ = l_Lean_Expr_isForall(v_joinTy_2859_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2869_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1, &l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1_once, _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1);
v___x_2870_ = l_Lean_MessageData_ofExpr(v_joinTy_2859_);
v___x_2871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2871_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = l_Lean_Expr_consumeMData(v_joinTy_2859_);
lean_dec_ref(v_joinTy_2859_);
v___x_2874_ = l_Lean_Expr_bindingBody_x21(v___x_2873_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v___x_2874_, v_resTy_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2885_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2885_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2880_ = lean_unsigned_to_nat(1u);
v___x_2881_ = lean_nat_add(v___x_2880_, v_a_2876_);
lean_dec(v_a_2876_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2881_);
v___x_2883_ = v___x_2878_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
else
{
return v___x_2875_;
}
}
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec_ref(v_joinTy_2859_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
}
else
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_Expr_consumeMData(v_joinTy_2859_);
lean_dec_ref(v_joinTy_2859_);
v_joinTy_2859_ = v___x_2888_;
goto _start;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_getNumJoinParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_joinTy_2859_ = stack[0].m_obj;
lean_object* v_resTy_2860_ = stack[1].m_obj;
lean_object* v_a_2861_ = stack[2].m_obj;
lean_object* v_a_2862_ = stack[3].m_obj;
lean_object* v_a_2863_ = stack[4].m_obj;
lean_object* v_a_2864_ = stack[5].m_obj;
lean_object* v_res_2890_;
v_res_2890_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v_joinTy_2859_, v_resTy_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
stack->m_obj
 = v_res_2890_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams___boxed(lean_object* v_joinTy_2891_, lean_object* v_resTy_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v_joinTy_2891_, v_resTy_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec_ref(v_resTy_2892_);
return v_res_2898_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(lean_object* v_lastReduction_2900_, lean_object* v_f_2901_, lean_object* v_rargs_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
switch(lean_obj_tag(v_f_2901_))
{
case 10:
{
lean_object* v_expr_2908_; 
v_expr_2908_ = lean_ctor_get(v_f_2901_, 1);
lean_inc_ref(v_expr_2908_);
lean_dec_ref_known(v_f_2901_, 2);
v_f_2901_ = v_expr_2908_;
goto _start;
}
case 5:
{
lean_object* v_fn_2910_; lean_object* v_arg_2911_; lean_object* v___x_2912_; 
v_fn_2910_ = lean_ctor_get(v_f_2901_, 0);
lean_inc_ref(v_fn_2910_);
v_arg_2911_ = lean_ctor_get(v_f_2901_, 1);
lean_inc_ref(v_arg_2911_);
lean_dec_ref_known(v_f_2901_, 2);
v___x_2912_ = lean_array_push(v_rargs_2902_, v_arg_2911_);
v_f_2901_ = v_fn_2910_;
v_rargs_2902_ = v___x_2912_;
goto _start;
}
case 6:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2914_ = lean_array_get_size(v_rargs_2902_);
v___x_2915_ = lean_unsigned_to_nat(0u);
v___x_2916_ = lean_nat_dec_eq(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v_e_x27_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_lastReduction_2900_);
v_e_x27_2917_ = l_Lean_Expr_betaRev(v_f_2901_, v_rargs_2902_, v___x_2916_, v___x_2916_);
lean_dec_ref(v_rargs_2902_);
lean_inc_ref(v_e_x27_2917_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_e_x27_2917_);
v___x_2919_ = l_Lean_Expr_getAppFn(v_e_x27_2917_);
v___x_2920_ = l_Lean_Expr_getAppNumArgs(v_e_x27_2917_);
v___x_2921_ = lean_mk_empty_array_with_capacity(v___x_2920_);
lean_dec(v___x_2920_);
v___x_2922_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_x27_2917_, v___x_2921_);
v_lastReduction_2900_ = v___x_2918_;
v_f_2901_ = v___x_2919_;
v_rargs_2902_ = v___x_2922_;
goto _start;
}
else
{
lean_object* v___x_2924_; 
lean_dec_ref_known(v_f_2901_, 3);
lean_dec_ref(v_rargs_2902_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v_lastReduction_2900_);
return v___x_2924_;
}
}
case 4:
{
lean_object* v_declName_2925_; lean_object* v___x_2926_; lean_object* v_env_2927_; lean_object* v___x_2928_; 
v_declName_2925_ = lean_ctor_get(v_f_2901_, 0);
v___x_2926_ = lean_st_ref_get(v_a_2906_);
v_env_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc_ref(v_env_2927_);
lean_dec(v___x_2926_);
lean_inc(v_declName_2925_);
v___x_2928_ = l_Lean_Environment_getProjectionStructureName_x3f(v_env_2927_, v_declName_2925_);
if (lean_obj_tag(v___x_2928_) == 1)
{
lean_object* v_val_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2963_; 
v_val_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_2963_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_val_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2963_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
if (lean_obj_tag(v_val_2929_) == 1)
{
lean_object* v_pre_2933_; 
v_pre_2933_ = lean_ctor_get(v_val_2929_, 0);
if (lean_obj_tag(v_pre_2933_) == 0)
{
lean_object* v_str_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v_str_2934_ = lean_ctor_get(v_val_2929_, 1);
lean_inc_ref(v_str_2934_);
lean_dec_ref_known(v_val_2929_, 2);
v___x_2935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___closed__0));
v___x_2936_ = lean_string_dec_eq(v_str_2934_, v___x_2935_);
lean_dec_ref(v_str_2934_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2938_; 
lean_dec_ref_known(v_f_2901_, 2);
lean_dec_ref(v_rargs_2902_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 0);
lean_ctor_set(v___x_2931_, 0, v_lastReduction_2900_);
v___x_2938_ = v___x_2931_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_lastReduction_2900_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
else
{
lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; 
lean_del_object(v___x_2931_);
v___x_2940_ = l_Lean_mkAppRev(v_f_2901_, v_rargs_2902_);
lean_dec_ref(v_rargs_2902_);
v___x_2941_ = 0;
v___x_2942_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_2940_, v___x_2941_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2956_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2956_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2956_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
if (lean_obj_tag(v_a_2943_) == 0)
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v_lastReduction_2900_);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_lastReduction_2900_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
else
{
lean_object* v_val_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_del_object(v___x_2945_);
v_val_2950_ = lean_ctor_get(v_a_2943_, 0);
lean_inc(v_val_2950_);
lean_dec_ref_known(v_a_2943_, 1);
v___x_2951_ = l_Lean_Expr_getAppFn(v_val_2950_);
v___x_2952_ = l_Lean_Expr_getAppNumArgs(v_val_2950_);
v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2952_);
lean_dec(v___x_2952_);
v___x_2954_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_val_2950_, v___x_2953_);
v_f_2901_ = v___x_2951_;
v_rargs_2902_ = v___x_2954_;
goto _start;
}
}
}
else
{
lean_dec(v_lastReduction_2900_);
return v___x_2942_;
}
}
}
else
{
lean_object* v___x_2958_; 
lean_dec_ref_known(v_val_2929_, 2);
lean_dec_ref_known(v_f_2901_, 2);
lean_dec_ref(v_rargs_2902_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 0);
lean_ctor_set(v___x_2931_, 0, v_lastReduction_2900_);
v___x_2958_ = v___x_2931_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_lastReduction_2900_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
else
{
lean_object* v___x_2961_; 
lean_dec(v_val_2929_);
lean_dec_ref_known(v_f_2901_, 2);
lean_dec_ref(v_rargs_2902_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 0);
lean_ctor_set(v___x_2931_, 0, v_lastReduction_2900_);
v___x_2961_ = v___x_2931_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_lastReduction_2900_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v___x_2964_; 
lean_dec(v___x_2928_);
lean_dec_ref_known(v_f_2901_, 2);
lean_dec_ref(v_rargs_2902_);
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v_lastReduction_2900_);
return v___x_2964_;
}
}
case 11:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Meta_reduceProj_x3f(v_f_2901_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2987_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2987_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2987_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
if (lean_obj_tag(v_a_2966_) == 0)
{
lean_object* v___x_2971_; 
lean_dec_ref(v_rargs_2902_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v_lastReduction_2900_);
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_lastReduction_2900_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
else
{
lean_object* v_val_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2986_; 
lean_del_object(v___x_2968_);
lean_dec(v_lastReduction_2900_);
v_val_2973_ = lean_ctor_get(v_a_2966_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_a_2966_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2975_ = v_a_2966_;
v_isShared_2976_ = v_isSharedCheck_2986_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_val_2973_);
lean_dec(v_a_2966_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2986_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = l_Lean_mkAppRev(v_val_2973_, v_rargs_2902_);
lean_dec_ref(v_rargs_2902_);
lean_inc_ref(v___x_2977_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2977_);
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2980_ = l_Lean_Expr_getAppFn(v___x_2977_);
v___x_2981_ = l_Lean_Expr_getAppNumArgs(v___x_2977_);
v___x_2982_ = lean_mk_empty_array_with_capacity(v___x_2981_);
lean_dec(v___x_2981_);
v___x_2983_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2977_, v___x_2982_);
v_lastReduction_2900_ = v___x_2979_;
v_f_2901_ = v___x_2980_;
v_rargs_2902_ = v___x_2983_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v_rargs_2902_);
lean_dec(v_lastReduction_2900_);
return v___x_2965_;
}
}
case 8:
{
lean_object* v_declName_2988_; lean_object* v_type_2989_; lean_object* v_value_2990_; lean_object* v_body_2991_; uint8_t v_nondep_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v_declName_2988_ = lean_ctor_get(v_f_2901_, 0);
lean_inc(v_declName_2988_);
v_type_2989_ = lean_ctor_get(v_f_2901_, 1);
lean_inc_ref(v_type_2989_);
v_value_2990_ = lean_ctor_get(v_f_2901_, 2);
lean_inc_ref(v_value_2990_);
v_body_2991_ = lean_ctor_get(v_f_2901_, 3);
lean_inc_ref(v_body_2991_);
v_nondep_2992_ = lean_ctor_get_uint8(v_f_2901_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_f_2901_, 4);
v___x_2993_ = lean_box(0);
v___x_2994_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_2993_, v_body_2991_, v_rargs_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3014_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3014_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3014_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
if (lean_obj_tag(v_a_2995_) == 0)
{
lean_object* v___x_3000_; 
lean_dec_ref(v_value_2990_);
lean_dec_ref(v_type_2989_);
lean_dec(v_declName_2988_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v_lastReduction_2900_);
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_lastReduction_2900_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
else
{
lean_object* v_val_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3013_; 
lean_dec(v_lastReduction_2900_);
v_val_3002_ = lean_ctor_get(v_a_2995_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_a_2995_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3004_ = v_a_2995_;
v_isShared_3005_ = v_isSharedCheck_3013_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_val_3002_);
lean_dec(v_a_2995_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3013_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3006_ = l_Lean_Expr_letE___override(v_declName_2988_, v_type_2989_, v_value_2990_, v_val_3002_, v_nondep_2992_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3006_);
v___x_3008_ = v___x_3004_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3008_);
v___x_3010_ = v___x_2997_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
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
}
else
{
lean_dec_ref(v_value_2990_);
lean_dec_ref(v_type_2989_);
lean_dec(v_declName_2988_);
lean_dec(v_lastReduction_2900_);
return v___x_2994_;
}
}
default: 
{
lean_object* v___x_3015_; 
lean_dec_ref(v_rargs_2902_);
lean_dec_ref(v_f_2901_);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_lastReduction_2900_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lastReduction_2900_ = stack[0].m_obj;
lean_object* v_f_2901_ = stack[1].m_obj;
lean_object* v_rargs_2902_ = stack[2].m_obj;
lean_object* v_a_2903_ = stack[3].m_obj;
lean_object* v_a_2904_ = stack[4].m_obj;
lean_object* v_a_2905_ = stack[5].m_obj;
lean_object* v_a_2906_ = stack[6].m_obj;
lean_object* v_res_3016_;
v_res_3016_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v_lastReduction_2900_, v_f_2901_, v_rargs_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
stack->m_obj
 = v_res_3016_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___boxed(lean_object* v_lastReduction_3017_, lean_object* v_f_3018_, lean_object* v_rargs_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v_lastReduction_3017_, v_f_3018_, v_rargs_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
return v_res_3025_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(lean_object* v_e_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = l_Lean_Expr_getAppFn(v_e_3026_);
v___x_3034_ = l_Lean_Expr_getAppNumArgs(v_e_3026_);
v___x_3035_ = lean_mk_empty_array_with_capacity(v___x_3034_);
lean_dec(v___x_3034_);
v___x_3036_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_3026_, v___x_3035_);
v___x_3037_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_3032_, v___x_3033_, v___x_3036_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
return v___x_3037_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3026_ = stack[0].m_obj;
lean_object* v_a_3027_ = stack[1].m_obj;
lean_object* v_a_3028_ = stack[2].m_obj;
lean_object* v_a_3029_ = stack[3].m_obj;
lean_object* v_a_3030_ = stack[4].m_obj;
lean_object* v_res_3038_;
v_res_3038_ = l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(v_e_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
stack->m_obj
 = v_res_3038_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f___boxed(lean_object* v_e_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(v_e_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3045_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set(v___x_3048_, 1, v___x_3046_);
return v___x_3048_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg(){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0);
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3052_;
v_res_3052_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
stack->m_obj
 = v_res_3052_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___boxed(lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v_res_3054_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(lean_object* v_00_u03b1_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v___x_3065_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3056_ = stack[1].m_obj;
lean_object* v___y_3057_ = stack[2].m_obj;
lean_object* v___y_3058_ = stack[3].m_obj;
lean_object* v___y_3059_ = stack[4].m_obj;
lean_object* v___y_3060_ = stack[5].m_obj;
lean_object* v___y_3061_ = stack[6].m_obj;
lean_object* v___y_3062_ = stack[7].m_obj;
lean_object* v___y_3063_ = stack[8].m_obj;
lean_object* v_res_3066_;
v_res_3066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(lean_box(0), v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
stack->m_obj
 = v_res_3066_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___boxed(lean_object* v_00_u03b1_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(v_00_u03b1_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
return v_res_3077_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(lean_object* v_as_3078_, size_t v_sz_3079_, size_t v_i_3080_, lean_object* v_b_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_a_3091_; uint8_t v___x_3095_; 
v___x_3095_ = lean_usize_dec_lt(v_i_3080_, v_sz_3079_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v_b_3081_);
return v___x_3096_;
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_a_3097_ = lean_array_uget_borrowed(v_as_3078_, v_i_3080_);
lean_inc(v_a_3097_);
v___x_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_a_3097_);
v___x_3099_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_b_3081_, v___x_3098_);
lean_dec_ref_known(v___x_3098_, 1);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_unsigned_to_nat(1000u);
v___x_3101_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3082_, v___y_3084_, v___y_3086_, v___y_3088_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
lean_inc(v_a_3097_);
v___x_3103_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_a_3097_, v___x_3100_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3105_; 
lean_dec(v_a_3102_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_b_3081_, v_a_3104_);
v_a_3091_ = v___x_3105_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3126_; 
v_a_3106_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3108_ = v___x_3103_;
v_isShared_3109_ = v_isSharedCheck_3126_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3103_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3126_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
uint8_t v___y_3111_; uint8_t v___x_3124_; 
v___x_3124_ = l_Lean_Exception_isInterrupt(v_a_3106_);
if (v___x_3124_ == 0)
{
uint8_t v___x_3125_; 
lean_inc(v_a_3106_);
v___x_3125_ = l_Lean_Exception_isRuntime(v_a_3106_);
v___y_3111_ = v___x_3125_;
goto v___jp_3110_;
}
else
{
v___y_3111_ = v___x_3124_;
goto v___jp_3110_;
}
v___jp_3110_:
{
if (v___y_3111_ == 0)
{
lean_object* v___x_3112_; 
lean_del_object(v___x_3108_);
lean_dec(v_a_3106_);
v___x_3112_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3102_, v___y_3111_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_dec_ref_known(v___x_3112_, 1);
v_a_3091_ = v_b_3081_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v_b_3081_);
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v___x_3122_; 
lean_dec(v_a_3102_);
lean_dec_ref(v_b_3081_);
if (v_isShared_3109_ == 0)
{
v___x_3122_ = v___x_3108_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3106_);
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
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v_b_3081_);
v_a_3127_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3101_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3101_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
v_a_3091_ = v_b_3081_;
goto v___jp_3090_;
}
}
v___jp_3090_:
{
size_t v___x_3092_; size_t v___x_3093_; 
v___x_3092_ = ((size_t)1ULL);
v___x_3093_ = lean_usize_add(v_i_3080_, v___x_3092_);
v_i_3080_ = v___x_3093_;
v_b_3081_ = v_a_3091_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3078_ = stack[0].m_obj;
size_t v_sz_3079_ = stack[1].m_num;
size_t v_i_3080_ = stack[2].m_num;
lean_object* v_b_3081_ = stack[3].m_obj;
lean_object* v___y_3082_ = stack[4].m_obj;
lean_object* v___y_3083_ = stack[5].m_obj;
lean_object* v___y_3084_ = stack[6].m_obj;
lean_object* v___y_3085_ = stack[7].m_obj;
lean_object* v___y_3086_ = stack[8].m_obj;
lean_object* v___y_3087_ = stack[9].m_obj;
lean_object* v___y_3088_ = stack[10].m_obj;
lean_object* v_res_3135_;
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_3078_, v_sz_3079_, v_i_3080_, v_b_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
stack->m_obj
 = v_res_3135_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg___boxed(lean_object* v_as_3136_, lean_object* v_sz_3137_, lean_object* v_i_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
size_t v_sz_boxed_3148_; size_t v_i_boxed_3149_; lean_object* v_res_3150_; 
v_sz_boxed_3148_ = lean_unbox_usize(v_sz_3137_);
lean_dec(v_sz_3137_);
v_i_boxed_3149_ = lean_unbox_usize(v_i_3138_);
lean_dec(v_i_3138_);
v_res_3150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_3136_, v_sz_boxed_3148_, v_i_boxed_3149_, v_b_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v_as_3136_);
return v_res_3150_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(lean_object* v_msg_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_ref_3157_; lean_object* v___x_3158_; lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3167_; 
v_ref_3157_ = lean_ctor_get(v___y_3154_, 2);
v___x_3158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3167_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_inc(v_ref_3157_);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v_ref_3157_);
lean_ctor_set(v___x_3163_, 1, v_a_3159_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 1);
lean_ctor_set(v___x_3161_, 0, v___x_3163_);
v___x_3165_ = v___x_3161_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3151_ = stack[0].m_obj;
lean_object* v___y_3152_ = stack[1].m_obj;
lean_object* v___y_3153_ = stack[2].m_obj;
lean_object* v___y_3154_ = stack[3].m_obj;
lean_object* v___y_3155_ = stack[4].m_obj;
lean_object* v_res_3168_;
v_res_3168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
stack->m_obj
 = v_res_3168_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg___boxed(lean_object* v_msg_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
return v_res_3175_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(lean_object* v_ref_3176_, lean_object* v_msg_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_toCold_3187_; lean_object* v_currRecDepth_3188_; lean_object* v_ref_3189_; uint16_t v_optionFlags_3190_; uint8_t v_suppressElabErrors_3191_; uint8_t v_isRecordingDeps_3192_; lean_object* v_ref_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_toCold_3187_ = lean_ctor_get(v___y_3184_, 0);
v_currRecDepth_3188_ = lean_ctor_get(v___y_3184_, 1);
v_ref_3189_ = lean_ctor_get(v___y_3184_, 2);
v_optionFlags_3190_ = lean_ctor_get_uint16(v___y_3184_, sizeof(void*)*3);
v_suppressElabErrors_3191_ = lean_ctor_get_uint8(v___y_3184_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3192_ = lean_ctor_get_uint8(v___y_3184_, sizeof(void*)*3 + 3);
v_ref_3193_ = l_Lean_replaceRef(v_ref_3176_, v_ref_3189_);
lean_inc(v_currRecDepth_3188_);
lean_inc_ref(v_toCold_3187_);
v___x_3194_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3194_, 0, v_toCold_3187_);
lean_ctor_set(v___x_3194_, 1, v_currRecDepth_3188_);
lean_ctor_set(v___x_3194_, 2, v_ref_3193_);
lean_ctor_set_uint16(v___x_3194_, sizeof(void*)*3, v_optionFlags_3190_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*3 + 2, v_suppressElabErrors_3191_);
lean_ctor_set_uint8(v___x_3194_, sizeof(void*)*3 + 3, v_isRecordingDeps_3192_);
v___x_3195_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3177_, v___y_3182_, v___y_3183_, v___x_3194_, v___y_3185_);
lean_dec_ref_known(v___x_3194_, 3);
return v___x_3195_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3176_ = stack[0].m_obj;
lean_object* v_msg_3177_ = stack[1].m_obj;
lean_object* v___y_3178_ = stack[2].m_obj;
lean_object* v___y_3179_ = stack[3].m_obj;
lean_object* v___y_3180_ = stack[4].m_obj;
lean_object* v___y_3181_ = stack[5].m_obj;
lean_object* v___y_3182_ = stack[6].m_obj;
lean_object* v___y_3183_ = stack[7].m_obj;
lean_object* v___y_3184_ = stack[8].m_obj;
lean_object* v___y_3185_ = stack[9].m_obj;
lean_object* v_res_3196_;
v_res_3196_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3176_, v_msg_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
stack->m_obj
 = v_res_3196_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_ref_3197_, lean_object* v_msg_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3197_, v_msg_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v_ref_3197_);
return v_res_3208_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0);
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3212_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3213_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
lean_ctor_set(v___x_3215_, 2, v___x_3214_);
lean_ctor_set(v___x_3215_, 3, v___x_3214_);
lean_ctor_set(v___x_3215_, 4, v___x_3213_);
lean_ctor_set(v___x_3215_, 5, v___x_3213_);
lean_ctor_set(v___x_3215_, 6, v___x_3213_);
lean_ctor_set(v___x_3215_, 7, v___x_3213_);
lean_ctor_set(v___x_3215_, 8, v___x_3213_);
lean_ctor_set(v___x_3215_, 9, v___x_3213_);
lean_ctor_set(v___x_3215_, 10, v___x_3213_);
lean_ctor_set(v___x_3215_, 11, v___x_3212_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = lean_unsigned_to_nat(32u);
v___x_3217_ = lean_mk_empty_array_with_capacity(v___x_3216_);
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3219_ = ((size_t)5ULL);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_unsigned_to_nat(32u);
v___x_3222_ = lean_mk_empty_array_with_capacity(v___x_3221_);
v___x_3223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3);
v___x_3224_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3222_);
lean_ctor_set(v___x_3224_, 2, v___x_3220_);
lean_ctor_set(v___x_3224_, 3, v___x_3220_);
lean_ctor_set_usize(v___x_3224_, 4, v___x_3219_);
return v___x_3224_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3225_ = lean_box(1);
v___x_3226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4);
v___x_3227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_3228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
lean_ctor_set(v___x_3228_, 2, v___x_3225_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__6));
v___x_3231_ = l_Lean_stringToMessageData(v___x_3230_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__8));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__10));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__12));
v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__14));
v___x_3243_ = l_Lean_stringToMessageData(v___x_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16));
v___x_3246_ = l_Lean_stringToMessageData(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__21(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__20));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__23(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__22));
v___x_3255_ = l_Lean_stringToMessageData(v___x_3254_);
return v___x_3255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__25(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__24));
v___x_3258_ = l_Lean_stringToMessageData(v___x_3257_);
return v___x_3258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__27(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__26));
v___x_3261_ = l_Lean_stringToMessageData(v___x_3260_);
return v___x_3261_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object* v_msg_3262_, lean_object* v_declHint_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v_env_3268_; uint8_t v___x_3269_; 
v___x_3266_ = lean_box(0);
v___x_3267_ = lean_st_ref_get(v___y_3264_);
v_env_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc_ref(v_env_3268_);
lean_dec(v___x_3267_);
v___x_3269_ = l_Lean_Name_isAnonymous(v_declHint_3263_);
if (v___x_3269_ == 0)
{
uint8_t v_isExporting_3270_; 
v_isExporting_3270_ = lean_ctor_get_uint8(v_env_3268_, sizeof(void*)*13);
if (v_isExporting_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3263_);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_msg_3262_);
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
lean_inc_ref(v_env_3268_);
v___x_3272_ = l_Lean_Environment_setExporting(v_env_3268_, v___x_3269_);
lean_inc(v_declHint_3263_);
lean_inc_ref(v___x_3272_);
v___x_3273_ = l_Lean_Environment_contains(v___x_3272_, v_declHint_3263_, v_isExporting_3270_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3263_);
v___x_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_msg_3262_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v_c_3280_; lean_object* v___x_3281_; 
v___x_3275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2);
v___x_3276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5);
v___x_3277_ = l_Lean_Options_empty;
v___x_3278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3272_);
lean_ctor_set(v___x_3278_, 1, v___x_3275_);
lean_ctor_set(v___x_3278_, 2, v___x_3276_);
lean_ctor_set(v___x_3278_, 3, v___x_3277_);
lean_inc(v_declHint_3263_);
v___x_3279_ = l_Lean_MessageData_ofConstName(v_declHint_3263_, v___x_3269_);
v_c_3280_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3280_, 0, v___x_3278_);
lean_ctor_set(v_c_3280_, 1, v___x_3279_);
v___x_3281_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3268_, v_declHint_3263_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3263_);
v___x_3282_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v_c_3280_);
v___x_3284_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Lean_MessageData_note(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_msg_3262_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
return v___x_3288_;
}
else
{
lean_object* v_val_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3345_; 
v_val_3289_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3291_ = v___x_3281_;
v_isShared_3292_ = v_isSharedCheck_3345_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_val_3289_);
lean_dec(v___x_3281_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3345_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v_modules_3294_; lean_object* v_moduleNames_3295_; lean_object* v_mod_3296_; uint8_t v___y_3298_; uint8_t v___x_3328_; 
v___x_3293_ = l_Lean_Environment_header(v_env_3268_);
lean_dec_ref(v_env_3268_);
v_modules_3294_ = lean_ctor_get(v___x_3293_, 3);
lean_inc_ref(v_modules_3294_);
v_moduleNames_3295_ = lean_ctor_get(v___x_3293_, 4);
lean_inc_ref(v_moduleNames_3295_);
lean_dec_ref(v___x_3293_);
v_mod_3296_ = lean_array_get(v___x_3266_, v_moduleNames_3295_, v_val_3289_);
lean_dec_ref(v_moduleNames_3295_);
v___x_3328_ = l_Lean_isPrivateName(v_declHint_3263_);
lean_dec(v_declHint_3263_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = lean_array_get_size(v_modules_3294_);
v___x_3330_ = lean_nat_dec_lt(v_val_3289_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_dec_ref(v_modules_3294_);
lean_dec(v_val_3289_);
v___y_3298_ = v___x_3328_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3331_; lean_object* v_toImport_3332_; uint8_t v_isExported_3333_; 
v___x_3331_ = lean_array_fget(v_modules_3294_, v_val_3289_);
lean_dec(v_val_3289_);
lean_dec_ref(v_modules_3294_);
v_toImport_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc_ref(v_toImport_3332_);
lean_dec(v___x_3331_);
v_isExported_3333_ = lean_ctor_get_uint8(v_toImport_3332_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3332_);
v___y_3298_ = v_isExported_3333_;
goto v___jp_3297_;
}
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v_modules_3294_);
lean_del_object(v___x_3291_);
lean_dec(v_val_3289_);
v___x_3334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v_c_3280_);
v___x_3336_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__25);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = l_Lean_MessageData_ofName(v_mod_3296_);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__27);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3339_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_MessageData_note(v___x_3341_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v_msg_3262_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
v___jp_3297_:
{
if (v___y_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v_c_3280_);
v___x_3301_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_Lean_MessageData_ofName(v_mod_3296_);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = l_Lean_MessageData_note(v___x_3306_);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v_msg_3262_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3308_);
v___x_3310_ = v___x_3291_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v_c_3280_);
v___x_3314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = l_Lean_MessageData_ofName(v_mod_3296_);
lean_inc_ref(v___x_3316_);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___x_3318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__21);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v___x_3316_);
v___x_3321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__23);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = l_Lean_MessageData_note(v___x_3322_);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_msg_3262_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3324_);
v___x_3326_ = v___x_3291_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
else
{
lean_object* v___x_3346_; 
lean_dec_ref(v_env_3268_);
lean_dec(v_declHint_3263_);
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_msg_3262_);
return v___x_3346_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3262_ = stack[0].m_obj;
lean_object* v_declHint_3263_ = stack[1].m_obj;
lean_object* v___y_3264_ = stack[2].m_obj;
lean_object* v_res_3347_;
v_res_3347_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3262_, v_declHint_3263_, v___y_3264_);
stack->m_obj
 = v_res_3347_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_msg_3348_, lean_object* v_declHint_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3348_, v_declHint_3349_, v___y_3350_);
lean_dec(v___y_3350_);
return v_res_3352_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(lean_object* v_msg_3353_, lean_object* v_declHint_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v___x_3364_; lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3374_; 
v___x_3364_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3353_, v_declHint_3354_, v___y_3362_);
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3367_ = v___x_3364_;
v_isShared_3368_ = v_isSharedCheck_3374_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3364_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3374_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3369_ = l_Lean_unknownIdentifierMessageTag;
v___x_3370_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
lean_ctor_set(v___x_3370_, 1, v_a_3365_);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3370_);
v___x_3372_ = v___x_3367_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3353_ = stack[0].m_obj;
lean_object* v_declHint_3354_ = stack[1].m_obj;
lean_object* v___y_3355_ = stack[2].m_obj;
lean_object* v___y_3356_ = stack[3].m_obj;
lean_object* v___y_3357_ = stack[4].m_obj;
lean_object* v___y_3358_ = stack[5].m_obj;
lean_object* v___y_3359_ = stack[6].m_obj;
lean_object* v___y_3360_ = stack[7].m_obj;
lean_object* v___y_3361_ = stack[8].m_obj;
lean_object* v___y_3362_ = stack[9].m_obj;
lean_object* v_res_3375_;
v_res_3375_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_3353_, v_declHint_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
stack->m_obj
 = v_res_3375_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_msg_3376_, lean_object* v_declHint_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_3376_, v_declHint_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
return v_res_3387_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3388_, lean_object* v_msg_3389_, lean_object* v_declHint_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; lean_object* v_a_3401_; lean_object* v___x_3402_; 
v___x_3400_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_3389_, v_declHint_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref(v___x_3400_);
v___x_3402_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3388_, v_a_3401_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
return v___x_3402_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3388_ = stack[0].m_obj;
lean_object* v_msg_3389_ = stack[1].m_obj;
lean_object* v_declHint_3390_ = stack[2].m_obj;
lean_object* v___y_3391_ = stack[3].m_obj;
lean_object* v___y_3392_ = stack[4].m_obj;
lean_object* v___y_3393_ = stack[5].m_obj;
lean_object* v___y_3394_ = stack[6].m_obj;
lean_object* v___y_3395_ = stack[7].m_obj;
lean_object* v___y_3396_ = stack[8].m_obj;
lean_object* v___y_3397_ = stack[9].m_obj;
lean_object* v___y_3398_ = stack[10].m_obj;
lean_object* v_res_3403_;
v_res_3403_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3388_, v_msg_3389_, v_declHint_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
stack->m_obj
 = v_res_3403_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3404_, lean_object* v_msg_3405_, lean_object* v_declHint_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3404_, v_msg_3405_, v_declHint_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v_ref_3404_);
return v_res_3416_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__0));
v___x_3419_ = l_Lean_stringToMessageData(v___x_3418_);
return v___x_3419_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(lean_object* v_ref_3420_, lean_object* v_constName_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; uint8_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3431_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1);
v___x_3432_ = 0;
lean_inc(v_constName_3421_);
v___x_3433_ = l_Lean_MessageData_ofConstName(v_constName_3421_, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3431_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3434_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3420_, v___x_3436_, v_constName_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3437_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3420_ = stack[0].m_obj;
lean_object* v_constName_3421_ = stack[1].m_obj;
lean_object* v___y_3422_ = stack[2].m_obj;
lean_object* v___y_3423_ = stack[3].m_obj;
lean_object* v___y_3424_ = stack[4].m_obj;
lean_object* v___y_3425_ = stack[5].m_obj;
lean_object* v___y_3426_ = stack[6].m_obj;
lean_object* v___y_3427_ = stack[7].m_obj;
lean_object* v___y_3428_ = stack[8].m_obj;
lean_object* v___y_3429_ = stack[9].m_obj;
lean_object* v_res_3438_;
v_res_3438_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3420_, v_constName_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
stack->m_obj
 = v_res_3438_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___boxed(lean_object* v_ref_3439_, lean_object* v_constName_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3439_, v_constName_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v_ref_3439_);
return v_res_3450_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(lean_object* v_constName_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_ref_3461_; lean_object* v___x_3462_; 
v_ref_3461_ = lean_ctor_get(v___y_3458_, 2);
v___x_3462_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3461_, v_constName_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
return v___x_3462_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3451_ = stack[0].m_obj;
lean_object* v___y_3452_ = stack[1].m_obj;
lean_object* v___y_3453_ = stack[2].m_obj;
lean_object* v___y_3454_ = stack[3].m_obj;
lean_object* v___y_3455_ = stack[4].m_obj;
lean_object* v___y_3456_ = stack[5].m_obj;
lean_object* v___y_3457_ = stack[6].m_obj;
lean_object* v___y_3458_ = stack[7].m_obj;
lean_object* v___y_3459_ = stack[8].m_obj;
lean_object* v_res_3463_;
v_res_3463_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
stack->m_obj
 = v_res_3463_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg___boxed(lean_object* v_constName_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3474_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(lean_object* v_fst_3475_, lean_object* v_fst_3476_, lean_object* v_specThm_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_proof_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_proof_3487_ = lean_ctor_get(v_specThm_3477_, 2);
lean_inc_ref(v_proof_3487_);
lean_dec_ref(v_specThm_3477_);
v___x_3488_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(v_fst_3475_, v_proof_3487_);
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3488_);
lean_ctor_set(v___x_3490_, 1, v_fst_3476_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3475_ = stack[0].m_obj;
lean_object* v_fst_3476_ = stack[1].m_obj;
lean_object* v_specThm_3477_ = stack[2].m_obj;
lean_object* v___y_3478_ = stack[3].m_obj;
lean_object* v___y_3479_ = stack[4].m_obj;
lean_object* v___y_3480_ = stack[5].m_obj;
lean_object* v___y_3481_ = stack[6].m_obj;
lean_object* v___y_3482_ = stack[7].m_obj;
lean_object* v___y_3483_ = stack[8].m_obj;
lean_object* v___y_3484_ = stack[9].m_obj;
lean_object* v___y_3485_ = stack[10].m_obj;
lean_object* v_res_3493_;
v_res_3493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3475_, v_fst_3476_, v_specThm_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
stack->m_obj
 = v_res_3493_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0___boxed(lean_object* v_fst_3494_, lean_object* v_fst_3495_, lean_object* v_specThm_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3494_, v_fst_3495_, v_specThm_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3506_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(lean_object* v_constName_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v_env_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; 
v___x_3517_ = lean_st_ref_get(v___y_3515_);
v_env_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc_ref(v_env_3518_);
lean_dec(v___x_3517_);
v___x_3519_ = 0;
lean_inc(v_constName_3507_);
v___x_3520_ = l_Lean_Environment_find_x3f(v_env_3518_, v_constName_3507_, v___x_3519_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
return v___x_3521_;
}
else
{
lean_object* v_val_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_constName_3507_);
v_val_3522_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3520_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_val_3522_);
lean_dec(v___x_3520_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set_tag(v___x_3524_, 0);
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_val_3522_);
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
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3507_ = stack[0].m_obj;
lean_object* v___y_3508_ = stack[1].m_obj;
lean_object* v___y_3509_ = stack[2].m_obj;
lean_object* v___y_3510_ = stack[3].m_obj;
lean_object* v___y_3511_ = stack[4].m_obj;
lean_object* v___y_3512_ = stack[5].m_obj;
lean_object* v___y_3513_ = stack[6].m_obj;
lean_object* v___y_3514_ = stack[7].m_obj;
lean_object* v___y_3515_ = stack[8].m_obj;
lean_object* v_res_3530_;
v_res_3530_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_constName_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
stack->m_obj
 = v_res_3530_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2___boxed(lean_object* v_constName_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_constName_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
return v_res_3541_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__7));
v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v___x_3563_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(lean_object* v_as_3565_, size_t v_sz_3566_, size_t v_i_3567_, lean_object* v_b_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_a_3579_; uint8_t v_starArg_3583_; 
v_starArg_3583_ = lean_usize_dec_lt(v_i_3567_, v_sz_3566_);
if (v_starArg_3583_ == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v_b_3568_);
return v___x_3584_;
}
else
{
lean_object* v_snd_3585_; lean_object* v_fst_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3886_; 
v_snd_3585_ = lean_ctor_get(v_b_3568_, 1);
v_fst_3586_ = lean_ctor_get(v_b_3568_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_b_3568_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3588_ = v_b_3568_;
v_isShared_3589_ = v_isSharedCheck_3886_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_snd_3585_);
lean_inc(v_fst_3586_);
lean_dec(v_b_3568_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3886_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v_fst_3590_; lean_object* v_snd_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3885_; 
v_fst_3590_ = lean_ctor_get(v_snd_3585_, 0);
v_snd_3591_ = lean_ctor_get(v_snd_3585_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_snd_3585_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3593_ = v_snd_3585_;
v_isShared_3594_ = v_isSharedCheck_3885_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_snd_3591_);
lean_inc(v_fst_3590_);
lean_dec(v_snd_3585_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3885_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v_fst_3596_; lean_object* v_snd_3597_; lean_object* v_fst_3605_; lean_object* v_snd_3606_; lean_object* v_fst_3610_; lean_object* v_snd_3611_; lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v___y_3621_; lean_object* v___y_3622_; uint8_t v___y_3623_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3614_ = lean_unsigned_to_nat(1u);
v_a_3615_ = lean_array_uget_borrowed(v_as_3565_, v_i_3567_);
lean_inc(v_a_3615_);
v___x_3650_ = l_Lean_Syntax_getKind(v_a_3615_);
v___x_3651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2));
v___x_3652_ = lean_name_eq(v___x_3650_, v___x_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4));
v___x_3654_ = lean_name_eq(v___x_3650_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; uint8_t v___x_3656_; 
lean_del_object(v___x_3593_);
lean_del_object(v___x_3588_);
v___x_3655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6));
v___x_3656_ = lean_name_eq(v___x_3650_, v___x_3655_);
lean_dec(v___x_3650_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_dec_ref_known(v___x_3657_, 1);
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v_fst_3590_);
lean_ctor_set(v___x_3658_, 1, v_snd_3591_);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v_fst_3586_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v_a_3579_ = v___x_3659_;
goto v___jp_3578_;
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3660_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3657_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3657_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec(v_snd_3591_);
lean_inc(v_a_3615_);
v___x_3668_ = lean_array_push(v_fst_3590_, v_a_3615_);
v___x_3669_ = lean_box(v_starArg_3583_);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3668_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_fst_3586_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v_a_3579_ = v___x_3671_;
goto v___jp_3578_;
}
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
lean_dec(v___x_3650_);
v___x_3672_ = lean_unsigned_to_nat(0u);
v___x_3673_ = l_Lean_Syntax_getArg(v_a_3615_, v___x_3672_);
v___x_3674_ = l_Lean_Syntax_isNone(v___x_3673_);
lean_dec(v___x_3673_);
if (v___x_3674_ == 0)
{
lean_del_object(v___x_3593_);
lean_del_object(v___x_3588_);
goto v___jp_3616_;
}
else
{
lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3675_ = l_Lean_Syntax_getArg(v_a_3615_, v___x_3614_);
v___x_3676_ = l_Lean_Syntax_isNone(v___x_3675_);
lean_dec(v___x_3675_);
if (v___x_3676_ == 0)
{
lean_del_object(v___x_3593_);
lean_del_object(v___x_3588_);
goto v___jp_3616_;
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3709_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3677_ = lean_unsigned_to_nat(2u);
v___x_3678_ = l_Lean_Syntax_getArg(v_a_3615_, v___x_3677_);
v___x_3774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__9));
v___x_3775_ = l_Lean_Meta_saveState___redArg(v___y_3574_, v___y_3576_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___x_3775_, 1);
lean_inc(v___x_3678_);
v___x_3777_ = l_Lean_Elab_Term_resolveId_x3f(v___x_3678_, v___x_3774_, v_starArg_3583_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_dec(v_a_3776_);
v___y_3709_ = v___x_3777_;
goto v___jp_3708_;
}
else
{
lean_object* v_a_3778_; uint8_t v___y_3780_; uint8_t v___x_3791_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v___x_3791_ = l_Lean_Exception_isInterrupt(v_a_3778_);
if (v___x_3791_ == 0)
{
uint8_t v___x_3792_; 
lean_inc(v_a_3778_);
v___x_3792_ = l_Lean_Exception_isRuntime(v_a_3778_);
v___y_3780_ = v___x_3792_;
goto v___jp_3779_;
}
else
{
v___y_3780_ = v___x_3791_;
goto v___jp_3779_;
}
v___jp_3779_:
{
if (v___y_3780_ == 0)
{
lean_object* v___x_3781_; 
lean_dec_ref_known(v___x_3777_, 1);
v___x_3781_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3776_, v___y_3574_, v___y_3576_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v___x_3782_; 
lean_dec_ref_known(v___x_3781_, 1);
lean_inc(v___x_3678_);
v___x_3782_ = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(v___x_3678_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
v___y_3709_ = v___x_3782_;
goto v___jp_3708_;
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec(v___x_3678_);
lean_del_object(v___x_3593_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_del_object(v___x_3588_);
lean_dec(v_fst_3586_);
v_a_3783_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3781_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3781_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_dec(v_a_3776_);
v___y_3709_ = v___x_3777_;
goto v___jp_3708_;
}
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v___x_3678_);
lean_del_object(v___x_3593_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_del_object(v___x_3588_);
lean_dec(v_fst_3586_);
v_a_3793_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3775_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3775_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
v___jp_3679_:
{
lean_object* v_toCold_3684_; lean_object* v_currRecDepth_3685_; lean_object* v_ref_3686_; uint16_t v_optionFlags_3687_; uint8_t v_suppressElabErrors_3688_; uint8_t v_isRecordingDeps_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v_ref_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v_toCold_3684_ = lean_ctor_get(v___y_3682_, 0);
v_currRecDepth_3685_ = lean_ctor_get(v___y_3682_, 1);
v_ref_3686_ = lean_ctor_get(v___y_3682_, 2);
v_optionFlags_3687_ = lean_ctor_get_uint16(v___y_3682_, sizeof(void*)*3);
v_suppressElabErrors_3688_ = lean_ctor_get_uint8(v___y_3682_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3689_ = lean_ctor_get_uint8(v___y_3682_, sizeof(void*)*3 + 3);
v___x_3690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8);
lean_inc(v___x_3678_);
v___x_3691_ = l_Lean_MessageData_ofSyntax(v___x_3678_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v_ref_3695_ = l_Lean_replaceRef(v___x_3678_, v_ref_3686_);
lean_dec(v___x_3678_);
lean_inc(v_currRecDepth_3685_);
lean_inc_ref(v_toCold_3684_);
v___x_3696_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3696_, 0, v_toCold_3684_);
lean_ctor_set(v___x_3696_, 1, v_currRecDepth_3685_);
lean_ctor_set(v___x_3696_, 2, v_ref_3695_);
lean_ctor_set_uint16(v___x_3696_, sizeof(void*)*3, v_optionFlags_3687_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*3 + 2, v_suppressElabErrors_3688_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*3 + 3, v_isRecordingDeps_3689_);
v___x_3697_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v___x_3694_, v___y_3680_, v___y_3681_, v___x_3696_, v___y_3683_);
lean_dec_ref_known(v___x_3696_, 3);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref_known(v___x_3697_, 1);
v___x_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3698_, 0, v_fst_3590_);
lean_ctor_set(v___x_3698_, 1, v_snd_3591_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v_fst_3586_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v_a_3579_ = v___x_3699_;
goto v___jp_3578_;
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3700_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3697_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3697_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
v___jp_3708_:
{
if (lean_obj_tag(v___y_3709_) == 0)
{
lean_object* v_a_3710_; 
v_a_3710_ = lean_ctor_get(v___y_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___y_3709_, 1);
if (lean_obj_tag(v_a_3710_) == 1)
{
lean_object* v_val_3711_; 
v_val_3711_ = lean_ctor_get(v_a_3710_, 0);
lean_inc(v_val_3711_);
lean_dec_ref_known(v_a_3710_, 1);
switch(lean_obj_tag(v_val_3711_))
{
case 4:
{
lean_object* v_declName_3712_; lean_object* v___x_3713_; 
lean_dec(v___x_3678_);
lean_del_object(v___x_3593_);
lean_del_object(v___x_3588_);
v_declName_3712_ = lean_ctor_get(v_val_3711_, 0);
lean_inc_n(v_declName_3712_, 2);
lean_dec_ref_known(v_val_3711_, 2);
v___x_3713_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_declName_3712_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_dec_ref_known(v___x_3713_, 1);
v___x_3714_ = lean_unsigned_to_nat(1000u);
v___x_3715_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3570_, v___y_3572_, v___y_3574_, v___y_3576_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_3712_, v___x_3714_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
lean_dec(v_a_3716_);
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_3586_, v_a_3718_);
v_fst_3605_ = v___x_3719_;
v_snd_3606_ = v_fst_3590_;
goto v___jp_3604_;
}
else
{
lean_object* v_a_3720_; uint8_t v___x_3721_; 
v_a_3720_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3721_ = l_Lean_Exception_isInterrupt(v_a_3720_);
if (v___x_3721_ == 0)
{
uint8_t v___x_3722_; 
lean_inc(v_a_3720_);
v___x_3722_ = l_Lean_Exception_isRuntime(v_a_3720_);
v___y_3621_ = v_a_3720_;
v___y_3622_ = v_a_3716_;
v___y_3623_ = v___x_3722_;
goto v___jp_3620_;
}
else
{
v___y_3621_ = v_a_3720_;
v___y_3622_ = v_a_3716_;
v___y_3623_ = v___x_3721_;
goto v___jp_3620_;
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec(v_declName_3712_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3723_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3715_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3715_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_declName_3712_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3731_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3713_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3713_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3739_; lean_object* v___x_3740_; 
lean_dec(v___x_3678_);
v_fvarId_3739_ = lean_ctor_get(v_val_3711_, 0);
lean_inc(v_fvarId_3739_);
v___x_3740_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_val_3711_, v___y_3573_, v___y_3575_, v___y_3576_);
lean_dec_ref_known(v_val_3711_, 1);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_dec_ref_known(v___x_3740_, 1);
v___x_3741_ = lean_unsigned_to_nat(1000u);
v___x_3742_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3570_, v___y_3572_, v___y_3574_, v___y_3576_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvarId_3739_, v___x_3741_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3746_; 
lean_dec(v_a_3743_);
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
v___x_3746_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_3586_, v_a_3745_);
v_fst_3596_ = v___x_3746_;
v_snd_3597_ = v_fst_3590_;
goto v___jp_3595_;
}
else
{
lean_object* v_a_3747_; uint8_t v___x_3748_; 
v_a_3747_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3744_, 1);
v___x_3748_ = l_Lean_Exception_isInterrupt(v_a_3747_);
if (v___x_3748_ == 0)
{
uint8_t v___x_3749_; 
lean_inc(v_a_3747_);
v___x_3749_ = l_Lean_Exception_isRuntime(v_a_3747_);
v___y_3636_ = v_a_3747_;
v___y_3637_ = v_a_3743_;
v___y_3638_ = v___x_3749_;
goto v___jp_3635_;
}
else
{
v___y_3636_ = v_a_3747_;
v___y_3637_ = v_a_3743_;
v___y_3638_ = v___x_3748_;
goto v___jp_3635_;
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_fvarId_3739_);
lean_del_object(v___x_3593_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_del_object(v___x_3588_);
lean_dec(v_fst_3586_);
v_a_3750_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3742_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3742_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_dec(v_fvarId_3739_);
lean_del_object(v___x_3593_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_del_object(v___x_3588_);
lean_dec(v_fst_3586_);
v_a_3758_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3740_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3740_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
default: 
{
lean_dec(v_val_3711_);
lean_del_object(v___x_3593_);
lean_del_object(v___x_3588_);
v___y_3680_ = v___y_3573_;
v___y_3681_ = v___y_3574_;
v___y_3682_ = v___y_3575_;
v___y_3683_ = v___y_3576_;
goto v___jp_3679_;
}
}
}
else
{
lean_dec(v_a_3710_);
lean_del_object(v___x_3593_);
lean_del_object(v___x_3588_);
v___y_3680_ = v___y_3573_;
v___y_3681_ = v___y_3574_;
v___y_3682_ = v___y_3575_;
v___y_3683_ = v___y_3576_;
goto v___jp_3679_;
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec(v___x_3678_);
lean_del_object(v___x_3593_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_del_object(v___x_3588_);
lean_dec(v_fst_3586_);
v_a_3766_ = lean_ctor_get(v___y_3709_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___y_3709_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___y_3709_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___y_3709_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
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
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec(v___x_3650_);
lean_del_object(v___x_3593_);
lean_del_object(v___x_3588_);
v___x_3801_ = l_Lean_Syntax_getArg(v_a_3615_, v___x_3614_);
v___x_3802_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3570_, v___y_3572_, v___y_3574_, v___y_3576_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3876_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3876_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3876_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___y_3808_; uint8_t v___y_3809_; lean_object* v_a_3824_; lean_object* v___y_3828_; lean_object* v___x_3834_; 
lean_inc(v___x_3801_);
v___x_3834_ = l_Lean_Elab_Term_isLocalIdent_x3f(v___x_3801_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
if (lean_obj_tag(v_a_3835_) == 1)
{
lean_object* v_val_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec(v___x_3801_);
v_val_3836_ = lean_ctor_get(v_a_3835_, 0);
lean_inc(v_val_3836_);
lean_dec_ref_known(v_a_3835_, 1);
v___x_3837_ = l_Lean_Expr_fvarId_x21(v_val_3836_);
lean_dec(v_val_3836_);
v___x_3838_ = lean_unsigned_to_nat(1000u);
v___x_3839_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_3837_, v___x_3838_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3841_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
lean_inc(v_fst_3590_);
lean_inc(v_fst_3586_);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3586_, v_fst_3590_, v_a_3840_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
v___y_3828_ = v___x_3841_;
goto v___jp_3827_;
}
else
{
lean_object* v_a_3842_; 
v_a_3842_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3839_, 1);
v_a_3824_ = v_a_3842_;
goto v___jp_3823_;
}
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_dec(v_a_3835_);
v___x_3843_ = lean_box(0);
v___x_3844_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3570_, v___y_3572_, v___y_3574_, v___y_3576_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3846_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
lean_inc(v___x_3801_);
v___x_3846_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_3801_, v___x_3843_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_dec(v_a_3845_);
lean_dec(v___x_3801_);
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
v___x_3848_ = lean_unsigned_to_nat(1000u);
v___x_3849_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_a_3847_, v___x_3848_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
lean_inc(v_fst_3590_);
lean_inc(v_fst_3586_);
v___x_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3586_, v_fst_3590_, v_a_3850_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
v___y_3828_ = v___x_3851_;
goto v___jp_3827_;
}
else
{
lean_object* v_a_3852_; 
v_a_3852_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3849_, 1);
v_a_3824_ = v_a_3852_;
goto v___jp_3823_;
}
}
else
{
lean_object* v_a_3853_; uint8_t v___y_3855_; uint8_t v___x_3872_; 
v_a_3853_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3846_, 1);
v___x_3872_ = l_Lean_Exception_isInterrupt(v_a_3853_);
if (v___x_3872_ == 0)
{
uint8_t v___x_3873_; 
lean_inc(v_a_3853_);
v___x_3873_ = l_Lean_Exception_isRuntime(v_a_3853_);
v___y_3855_ = v___x_3873_;
goto v___jp_3854_;
}
else
{
v___y_3855_ = v___x_3872_;
goto v___jp_3854_;
}
v___jp_3854_:
{
if (v___y_3855_ == 0)
{
lean_object* v___x_3856_; 
lean_dec(v_a_3853_);
v___x_3856_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3845_, v___y_3855_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_toCold_3857_; lean_object* v_currRecDepth_3858_; lean_object* v_ref_3859_; uint16_t v_optionFlags_3860_; uint8_t v_suppressElabErrors_3861_; uint8_t v_isRecordingDeps_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v_ref_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
lean_dec_ref_known(v___x_3856_, 1);
v_toCold_3857_ = lean_ctor_get(v___y_3575_, 0);
v_currRecDepth_3858_ = lean_ctor_get(v___y_3575_, 1);
v_ref_3859_ = lean_ctor_get(v___y_3575_, 2);
v_optionFlags_3860_ = lean_ctor_get_uint16(v___y_3575_, sizeof(void*)*3);
v_suppressElabErrors_3861_ = lean_ctor_get_uint8(v___y_3575_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3862_ = lean_ctor_get_uint8(v___y_3575_, sizeof(void*)*3 + 3);
v___x_3863_ = l_Lean_Syntax_getId(v___x_3801_);
v___x_3864_ = l_Lean_Name_eraseMacroScopes(v___x_3863_);
lean_dec(v___x_3863_);
v_ref_3865_ = l_Lean_replaceRef(v___x_3801_, v_ref_3859_);
lean_dec(v___x_3801_);
lean_inc(v_currRecDepth_3858_);
lean_inc_ref(v_toCold_3857_);
v___x_3866_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3866_, 0, v_toCold_3857_);
lean_ctor_set(v___x_3866_, 1, v_currRecDepth_3858_);
lean_ctor_set(v___x_3866_, 2, v_ref_3865_);
lean_ctor_set_uint16(v___x_3866_, sizeof(void*)*3, v_optionFlags_3860_);
lean_ctor_set_uint8(v___x_3866_, sizeof(void*)*3 + 2, v_suppressElabErrors_3861_);
lean_ctor_set_uint8(v___x_3866_, sizeof(void*)*3 + 3, v_isRecordingDeps_3862_);
v___x_3867_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v___x_3864_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___x_3866_, v___y_3576_);
lean_dec_ref_known(v___x_3866_, 3);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3869_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
lean_inc(v_fst_3590_);
lean_inc(v_fst_3586_);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3586_, v_fst_3590_, v_a_3868_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
v___y_3828_ = v___x_3869_;
goto v___jp_3827_;
}
else
{
lean_object* v_a_3870_; 
v_a_3870_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3867_, 1);
v_a_3824_ = v_a_3870_;
goto v___jp_3823_;
}
}
else
{
lean_object* v_a_3871_; 
lean_dec(v___x_3801_);
v_a_3871_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3856_, 1);
v_a_3824_ = v_a_3871_;
goto v___jp_3823_;
}
}
else
{
lean_dec(v_a_3845_);
lean_dec(v___x_3801_);
v_a_3824_ = v_a_3853_;
goto v___jp_3823_;
}
}
}
}
else
{
lean_object* v_a_3874_; 
lean_dec(v___x_3801_);
v_a_3874_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3844_, 1);
v_a_3824_ = v_a_3874_;
goto v___jp_3823_;
}
}
}
else
{
lean_object* v_a_3875_; 
lean_dec(v___x_3801_);
v_a_3875_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3834_, 1);
v_a_3824_ = v_a_3875_;
goto v___jp_3823_;
}
v___jp_3807_:
{
if (v___y_3809_ == 0)
{
lean_object* v___x_3810_; 
lean_dec_ref(v___y_3808_);
lean_del_object(v___x_3805_);
v___x_3810_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3803_, v___y_3809_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v___x_3811_; 
lean_dec_ref_known(v___x_3810_, 1);
lean_inc(v_a_3615_);
v___x_3811_ = lean_array_push(v_fst_3590_, v_a_3615_);
v_fst_3610_ = v_fst_3586_;
v_snd_3611_ = v___x_3811_;
goto v___jp_3609_;
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3812_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3810_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3810_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v___x_3821_; 
lean_dec(v_a_3803_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set_tag(v___x_3805_, 1);
lean_ctor_set(v___x_3805_, 0, v___y_3808_);
v___x_3821_ = v___x_3805_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___y_3808_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
v___jp_3823_:
{
uint8_t v___x_3825_; 
v___x_3825_ = l_Lean_Exception_isInterrupt(v_a_3824_);
if (v___x_3825_ == 0)
{
uint8_t v___x_3826_; 
lean_inc_ref(v_a_3824_);
v___x_3826_ = l_Lean_Exception_isRuntime(v_a_3824_);
v___y_3808_ = v_a_3824_;
v___y_3809_ = v___x_3826_;
goto v___jp_3807_;
}
else
{
v___y_3808_ = v_a_3824_;
v___y_3809_ = v___x_3825_;
goto v___jp_3807_;
}
}
v___jp_3827_:
{
if (lean_obj_tag(v___y_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v_snd_3830_; lean_object* v_fst_3831_; lean_object* v_snd_3832_; 
lean_del_object(v___x_3805_);
lean_dec(v_a_3803_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3829_ = lean_ctor_get(v___y_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___y_3828_, 1);
v_snd_3830_ = lean_ctor_get(v_a_3829_, 1);
lean_inc(v_snd_3830_);
lean_dec(v_a_3829_);
v_fst_3831_ = lean_ctor_get(v_snd_3830_, 0);
lean_inc(v_fst_3831_);
v_snd_3832_ = lean_ctor_get(v_snd_3830_, 1);
lean_inc(v_snd_3832_);
lean_dec(v_snd_3830_);
v_fst_3610_ = v_fst_3831_;
v_snd_3611_ = v_snd_3832_;
goto v___jp_3609_;
}
else
{
lean_object* v_a_3833_; 
v_a_3833_ = lean_ctor_get(v___y_3828_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___y_3828_, 1);
v_a_3824_ = v_a_3833_;
goto v___jp_3823_;
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v___x_3801_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3877_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3802_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3802_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
v___jp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v_snd_3597_);
v___x_3599_ = v___x_3593_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_snd_3597_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_snd_3591_);
v___x_3599_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3601_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 1, v___x_3599_);
lean_ctor_set(v___x_3588_, 0, v_fst_3596_);
v___x_3601_ = v___x_3588_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_fst_3596_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v_a_3579_ = v___x_3601_;
goto v___jp_3578_;
}
}
}
v___jp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v_snd_3606_);
lean_ctor_set(v___x_3607_, 1, v_snd_3591_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_fst_3605_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v_a_3579_ = v___x_3608_;
goto v___jp_3578_;
}
v___jp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v_snd_3611_);
lean_ctor_set(v___x_3612_, 1, v_snd_3591_);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v_fst_3610_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v_a_3579_ = v___x_3613_;
goto v___jp_3578_;
}
v___jp_3616_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_inc(v_a_3615_);
v___x_3617_ = lean_array_push(v_fst_3590_, v_a_3615_);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v_snd_3591_);
v___x_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3619_, 0, v_fst_3586_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v_a_3579_ = v___x_3619_;
goto v___jp_3578_;
}
v___jp_3620_:
{
if (v___y_3623_ == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref(v___y_3621_);
v___x_3624_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_3622_, v___y_3623_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v___x_3625_; 
lean_dec_ref_known(v___x_3624_, 1);
lean_inc(v_a_3615_);
v___x_3625_ = lean_array_push(v_fst_3590_, v_a_3615_);
v_fst_3605_ = v_fst_3586_;
v_snd_3606_ = v___x_3625_;
goto v___jp_3604_;
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v_a_3626_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3624_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3624_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_object* v___x_3634_; 
lean_dec_ref(v___y_3622_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_dec(v_fst_3586_);
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___y_3621_);
return v___x_3634_;
}
}
v___jp_3635_:
{
if (v___y_3638_ == 0)
{
lean_object* v___x_3639_; 
lean_dec_ref(v___y_3636_);
v___x_3639_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_3637_, v___y_3638_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v___x_3640_; 
lean_dec_ref_known(v___x_3639_, 1);
lean_inc(v_a_3615_);
v___x_3640_ = lean_array_push(v_fst_3590_, v_a_3615_);
v_fst_3596_ = v_fst_3586_;
v_snd_3597_ = v___x_3640_;
goto v___jp_3595_;
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_del_object(v___x_3593_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_del_object(v___x_3588_);
lean_dec(v_fst_3586_);
v_a_3641_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3639_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3639_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
else
{
lean_object* v___x_3649_; 
lean_dec_ref(v___y_3637_);
lean_del_object(v___x_3593_);
lean_dec(v_snd_3591_);
lean_dec(v_fst_3590_);
lean_del_object(v___x_3588_);
lean_dec(v_fst_3586_);
v___x_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___y_3636_);
return v___x_3649_;
}
}
}
}
}
v___jp_3578_:
{
size_t v___x_3580_; size_t v___x_3581_; 
v___x_3580_ = ((size_t)1ULL);
v___x_3581_ = lean_usize_add(v_i_3567_, v___x_3580_);
v_i_3567_ = v___x_3581_;
v_b_3568_ = v_a_3579_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3565_ = stack[0].m_obj;
size_t v_sz_3566_ = stack[1].m_num;
size_t v_i_3567_ = stack[2].m_num;
lean_object* v_b_3568_ = stack[3].m_obj;
lean_object* v___y_3569_ = stack[4].m_obj;
lean_object* v___y_3570_ = stack[5].m_obj;
lean_object* v___y_3571_ = stack[6].m_obj;
lean_object* v___y_3572_ = stack[7].m_obj;
lean_object* v___y_3573_ = stack[8].m_obj;
lean_object* v___y_3574_ = stack[9].m_obj;
lean_object* v___y_3575_ = stack[10].m_obj;
lean_object* v___y_3576_ = stack[11].m_obj;
lean_object* v_res_3887_;
v_res_3887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v_as_3565_, v_sz_3566_, v_i_3567_, v_b_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
stack->m_obj
 = v_res_3887_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___boxed(lean_object* v_as_3888_, lean_object* v_sz_3889_, lean_object* v_i_3890_, lean_object* v_b_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
size_t v_sz_boxed_3901_; size_t v_i_boxed_3902_; lean_object* v_res_3903_; 
v_sz_boxed_3901_ = lean_unbox_usize(v_sz_3889_);
lean_dec(v_sz_3889_);
v_i_boxed_3902_ = lean_unbox_usize(v_i_3890_);
lean_dec(v_i_3890_);
v_res_3903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v_as_3888_, v_sz_boxed_3901_, v_i_boxed_3902_, v_b_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec_ref(v_as_3888_);
return v_res_3903_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15(void){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14));
v___x_3944_ = l_String_toRawSubstring_x27(v___x_3943_);
return v___x_3944_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20));
v___x_3956_ = l_String_toRawSubstring_x27(v___x_3955_);
return v___x_3956_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23(void){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Array_mkArray0___redArg();
return v___x_3959_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext(lean_object* v_optConfig_3964_, lean_object* v_lemmas_3965_, uint8_t v_ignoreStarArg_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
uint8_t v_starArg_3976_; uint8_t v_starArg_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_starArg_3976_ = 1;
v_starArg_3977_ = 0;
v___x_3978_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0));
v___x_3979_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_optConfig_3964_, v___x_3978_, v_starArg_3976_, v_a_3967_, v_a_3973_, v_a_3974_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3981_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3974_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; size_t v_sz_3988_; size_t v___x_3989_; lean_object* v___x_3990_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = l_Lean_Syntax_getArg(v_lemmas_3965_, v___x_3983_);
v___x_3985_ = l_Lean_Syntax_getSepArgs(v___x_3984_);
lean_dec(v___x_3984_);
v___x_3986_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2));
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v_a_3982_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v_sz_3988_ = lean_array_size(v___x_3985_);
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v___x_3985_, v_sz_3988_, v___x_3989_, v___x_3987_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec_ref(v___x_3985_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v_snd_3992_; lean_object* v_toCold_3993_; lean_object* v_fst_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4101_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref_known(v___x_3990_, 1);
v_snd_3992_ = lean_ctor_get(v_a_3991_, 1);
lean_inc(v_snd_3992_);
v_toCold_3993_ = lean_ctor_get(v_a_3973_, 0);
v_fst_3994_ = lean_ctor_get(v_a_3991_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v_a_3991_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; 
v_unused_4102_ = lean_ctor_get(v_a_3991_, 1);
lean_dec(v_unused_4102_);
v___x_3996_ = v_a_3991_;
v_isShared_3997_ = v_isSharedCheck_4101_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_fst_3994_);
lean_dec(v_a_3991_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4101_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_fst_3998_; lean_object* v_snd_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4100_; 
v_fst_3998_ = lean_ctor_get(v_snd_3992_, 0);
v_snd_3999_ = lean_ctor_get(v_snd_3992_, 1);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_snd_3992_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4001_ = v_snd_3992_;
v_isShared_4002_ = v_isSharedCheck_4100_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_snd_3999_);
lean_inc(v_fst_3998_);
lean_dec(v_snd_3992_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4100_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v_ref_4003_; lean_object* v_quotContext_4004_; lean_object* v_currMacroScope_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4010_; 
v_ref_4003_ = lean_ctor_get(v_a_3973_, 2);
v_quotContext_4004_ = lean_ctor_get(v_toCold_3993_, 8);
v_currMacroScope_4005_ = lean_ctor_get(v_toCold_3993_, 9);
v___x_4006_ = l_Lean_SourceInfo_fromRef(v_ref_4003_, v_starArg_3977_);
v___x_4007_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3));
v___x_4008_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4));
lean_inc(v___x_4006_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set_tag(v___x_4001_, 2);
lean_ctor_set(v___x_4001_, 1, v___x_4007_);
lean_ctor_set(v___x_4001_, 0, v___x_4006_);
v___x_4010_ = v___x_4001_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v___x_4007_);
v___x_4010_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4017_; 
v___x_4011_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6));
v___x_4012_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8));
v___x_4013_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10));
v___x_4014_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12));
v___x_4015_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13));
lean_inc(v___x_4006_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set_tag(v___x_3996_, 2);
lean_ctor_set(v___x_3996_, 1, v___x_4015_);
lean_ctor_set(v___x_3996_, 0, v___x_4006_);
v___x_4017_ = v___x_3996_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4098_, 1, v___x_4015_);
v___x_4017_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4018_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15);
v___x_4019_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16));
lean_inc_n(v_currMacroScope_4005_, 2);
lean_inc_n(v_quotContext_4004_, 2);
v___x_4020_ = l_Lean_addMacroScope(v_quotContext_4004_, v___x_4019_, v_currMacroScope_4005_);
v___x_4021_ = lean_box(0);
lean_inc_n(v___x_4006_, 14);
v___x_4022_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4006_);
lean_ctor_set(v___x_4022_, 1, v___x_4018_);
lean_ctor_set(v___x_4022_, 2, v___x_4020_);
lean_ctor_set(v___x_4022_, 3, v___x_4021_);
v___x_4023_ = l_Lean_Syntax_node2(v___x_4006_, v___x_4014_, v___x_4017_, v___x_4022_);
v___x_4024_ = l_Lean_Syntax_node1(v___x_4006_, v___x_4013_, v___x_4023_);
v___x_4025_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18));
v___x_4026_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19));
v___x_4027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4006_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21);
v___x_4029_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22));
v___x_4030_ = l_Lean_addMacroScope(v_quotContext_4004_, v___x_4029_, v_currMacroScope_4005_);
v___x_4031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4006_);
lean_ctor_set(v___x_4031_, 1, v___x_4028_);
lean_ctor_set(v___x_4031_, 2, v___x_4030_);
lean_ctor_set(v___x_4031_, 3, v___x_4021_);
v___x_4032_ = l_Lean_Syntax_node2(v___x_4006_, v___x_4025_, v___x_4027_, v___x_4031_);
v___x_4033_ = l_Lean_Syntax_node1(v___x_4006_, v___x_4013_, v___x_4032_);
v___x_4034_ = l_Lean_Syntax_node2(v___x_4006_, v___x_4012_, v___x_4024_, v___x_4033_);
v___x_4035_ = l_Lean_Syntax_node1(v___x_4006_, v___x_4011_, v___x_4034_);
v___x_4036_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23);
v___x_4037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4006_);
lean_ctor_set(v___x_4037_, 1, v___x_4012_);
lean_ctor_set(v___x_4037_, 2, v___x_4036_);
v___x_4038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24));
v___x_4039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4006_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25));
v___x_4041_ = l_Lean_Syntax_SepArray_ofElems(v___x_4040_, v_fst_3998_);
lean_dec(v_fst_3998_);
v___x_4042_ = l_Array_append___redArg(v___x_4036_, v___x_4041_);
lean_dec_ref(v___x_4041_);
v___x_4043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4006_);
lean_ctor_set(v___x_4043_, 1, v___x_4012_);
lean_ctor_set(v___x_4043_, 2, v___x_4042_);
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26));
v___x_4045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4006_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = l_Lean_Syntax_node3(v___x_4006_, v___x_4012_, v___x_4039_, v___x_4043_, v___x_4045_);
lean_inc_ref_n(v___x_4037_, 2);
v___x_4047_ = l_Lean_Syntax_node6(v___x_4006_, v___x_4008_, v___x_4010_, v___x_4035_, v___x_4037_, v___x_4037_, v___x_4046_, v___x_4037_);
v___x_4048_ = 0;
v___x_4049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__27));
v___x_4050_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_4047_, v_starArg_3977_, v___x_4048_, v_ignoreStarArg_3966_, v___x_4049_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec(v___x_4047_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4089_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4053_ = v___x_4050_;
v_isShared_4054_ = v_isSharedCheck_4089_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4050_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4089_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v_specThms_4056_; lean_object* v___y_4057_; uint8_t v___x_4067_; 
v___x_4067_ = lean_unbox(v_snd_3999_);
lean_dec(v_snd_3999_);
if (v___x_4067_ == 0)
{
v_specThms_4056_ = v_fst_3994_;
v___y_4057_ = v_a_3971_;
goto v___jp_4055_;
}
else
{
if (v_ignoreStarArg_3966_ == 0)
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Meta_getPropHyps(v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; size_t v_sz_4070_; lean_object* v___x_4071_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v_sz_4070_ = lean_array_size(v_a_4069_);
v___x_4071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_a_4069_, v_sz_4070_, v___x_3989_, v_fst_3994_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec(v_a_4069_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v_specThms_4056_ = v_a_4072_;
v___y_4057_ = v_a_3971_;
goto v___jp_4055_;
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_del_object(v___x_4053_);
lean_dec(v_a_4051_);
lean_dec(v_a_3980_);
v_a_4073_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4071_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4071_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_del_object(v___x_4053_);
lean_dec(v_a_4051_);
lean_dec(v_fst_3994_);
lean_dec(v_a_3980_);
v_a_4081_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4068_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4068_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
v_specThms_4056_ = v_fst_3994_;
v___y_4057_ = v_a_3971_;
goto v___jp_4055_;
}
}
v___jp_4055_:
{
lean_object* v_lctx_4058_; lean_object* v_ctx_4059_; lean_object* v_simprocs_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
v_lctx_4058_ = lean_ctor_get(v___y_4057_, 2);
v_ctx_4059_ = lean_ctor_get(v_a_4051_, 0);
lean_inc_ref(v_ctx_4059_);
v_simprocs_4060_ = lean_ctor_get(v_a_4051_, 1);
lean_inc_ref(v_simprocs_4060_);
lean_dec(v_a_4051_);
v___x_4061_ = lean_box(1);
lean_inc_ref(v_lctx_4058_);
v___x_4062_ = lean_local_ctx_num_indices(v_lctx_4058_);
v___x_4063_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4063_, 0, v_a_3980_);
lean_ctor_set(v___x_4063_, 1, v_specThms_4056_);
lean_ctor_set(v___x_4063_, 2, v_ctx_4059_);
lean_ctor_set(v___x_4063_, 3, v_simprocs_4060_);
lean_ctor_set(v___x_4063_, 4, v___x_4061_);
lean_ctor_set(v___x_4063_, 5, v___x_4062_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4063_);
v___x_4065_ = v___x_4053_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_snd_3999_);
lean_dec(v_fst_3994_);
lean_dec(v_a_3980_);
v_a_4090_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4050_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4050_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
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
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_3980_);
v_a_4103_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_3990_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_3990_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec(v_a_3980_);
v_a_4111_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_3981_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_3981_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
v_a_4119_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_3979_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_3979_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_mkSpecContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_optConfig_3964_ = stack[0].m_obj;
lean_object* v_lemmas_3965_ = stack[1].m_obj;
uint8_t v_ignoreStarArg_3966_ = stack[2].m_num;
lean_object* v_a_3967_ = stack[3].m_obj;
lean_object* v_a_3968_ = stack[4].m_obj;
lean_object* v_a_3969_ = stack[5].m_obj;
lean_object* v_a_3970_ = stack[6].m_obj;
lean_object* v_a_3971_ = stack[7].m_obj;
lean_object* v_a_3972_ = stack[8].m_obj;
lean_object* v_a_3973_ = stack[9].m_obj;
lean_object* v_a_3974_ = stack[10].m_obj;
lean_object* v_res_4127_;
v_res_4127_ = l_Lean_Elab_Tactic_Do_mkSpecContext(v_optConfig_3964_, v_lemmas_3965_, v_ignoreStarArg_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
stack->m_obj
 = v_res_4127_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___boxed(lean_object* v_optConfig_4128_, lean_object* v_lemmas_4129_, lean_object* v_ignoreStarArg_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
uint8_t v_ignoreStarArg_boxed_4140_; lean_object* v_res_4141_; 
v_ignoreStarArg_boxed_4140_ = lean_unbox(v_ignoreStarArg_4130_);
v_res_4141_ = l_Lean_Elab_Tactic_Do_mkSpecContext(v_optConfig_4128_, v_lemmas_4129_, v_ignoreStarArg_boxed_4140_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
lean_dec(v_lemmas_4129_);
return v_res_4141_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(lean_object* v_00_u03b1_4142_, lean_object* v_msg_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_4143_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
return v___x_4153_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4143_ = stack[1].m_obj;
lean_object* v___y_4144_ = stack[2].m_obj;
lean_object* v___y_4145_ = stack[3].m_obj;
lean_object* v___y_4146_ = stack[4].m_obj;
lean_object* v___y_4147_ = stack[5].m_obj;
lean_object* v___y_4148_ = stack[6].m_obj;
lean_object* v___y_4149_ = stack[7].m_obj;
lean_object* v___y_4150_ = stack[8].m_obj;
lean_object* v___y_4151_ = stack[9].m_obj;
lean_object* v_res_4154_;
v_res_4154_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(lean_box(0), v_msg_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
stack->m_obj
 = v_res_4154_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___boxed(lean_object* v_00_u03b1_4155_, lean_object* v_msg_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(v_00_u03b1_4155_, v_msg_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
return v_res_4166_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(lean_object* v_00_u03b1_4167_, lean_object* v_constName_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4178_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_4168_ = stack[1].m_obj;
lean_object* v___y_4169_ = stack[2].m_obj;
lean_object* v___y_4170_ = stack[3].m_obj;
lean_object* v___y_4171_ = stack[4].m_obj;
lean_object* v___y_4172_ = stack[5].m_obj;
lean_object* v___y_4173_ = stack[6].m_obj;
lean_object* v___y_4174_ = stack[7].m_obj;
lean_object* v___y_4175_ = stack[8].m_obj;
lean_object* v___y_4176_ = stack[9].m_obj;
lean_object* v_res_4179_;
v_res_4179_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(lean_box(0), v_constName_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
stack->m_obj
 = v_res_4179_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___boxed(lean_object* v_00_u03b1_4180_, lean_object* v_constName_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(v_00_u03b1_4180_, v_constName_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
return v_res_4191_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(lean_object* v_as_4192_, size_t v_sz_4193_, size_t v_i_4194_, lean_object* v_b_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_4192_, v_sz_4193_, v_i_4194_, v_b_4195_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4192_ = stack[0].m_obj;
size_t v_sz_4193_ = stack[1].m_num;
size_t v_i_4194_ = stack[2].m_num;
lean_object* v_b_4195_ = stack[3].m_obj;
lean_object* v___y_4196_ = stack[4].m_obj;
lean_object* v___y_4197_ = stack[5].m_obj;
lean_object* v___y_4198_ = stack[6].m_obj;
lean_object* v___y_4199_ = stack[7].m_obj;
lean_object* v___y_4200_ = stack[8].m_obj;
lean_object* v___y_4201_ = stack[9].m_obj;
lean_object* v___y_4202_ = stack[10].m_obj;
lean_object* v___y_4203_ = stack[11].m_obj;
lean_object* v_res_4206_;
v_res_4206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(v_as_4192_, v_sz_4193_, v_i_4194_, v_b_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
stack->m_obj
 = v_res_4206_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___boxed(lean_object* v_as_4207_, lean_object* v_sz_4208_, lean_object* v_i_4209_, lean_object* v_b_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
size_t v_sz_boxed_4220_; size_t v_i_boxed_4221_; lean_object* v_res_4222_; 
v_sz_boxed_4220_ = lean_unbox_usize(v_sz_4208_);
lean_dec(v_sz_4208_);
v_i_boxed_4221_ = lean_unbox_usize(v_i_4209_);
lean_dec(v_i_4209_);
v_res_4222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(v_as_4207_, v_sz_boxed_4220_, v_i_boxed_4221_, v_b_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec_ref(v_as_4207_);
return v_res_4222_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(lean_object* v_00_u03b1_4223_, lean_object* v_ref_4224_, lean_object* v_constName_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_4224_, v_constName_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4224_ = stack[1].m_obj;
lean_object* v_constName_4225_ = stack[2].m_obj;
lean_object* v___y_4226_ = stack[3].m_obj;
lean_object* v___y_4227_ = stack[4].m_obj;
lean_object* v___y_4228_ = stack[5].m_obj;
lean_object* v___y_4229_ = stack[6].m_obj;
lean_object* v___y_4230_ = stack[7].m_obj;
lean_object* v___y_4231_ = stack[8].m_obj;
lean_object* v___y_4232_ = stack[9].m_obj;
lean_object* v___y_4233_ = stack[10].m_obj;
lean_object* v_res_4236_;
v_res_4236_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(lean_box(0), v_ref_4224_, v_constName_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
stack->m_obj
 = v_res_4236_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___boxed(lean_object* v_00_u03b1_4237_, lean_object* v_ref_4238_, lean_object* v_constName_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(v_00_u03b1_4237_, v_ref_4238_, v_constName_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v_ref_4238_);
return v_res_4249_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_4250_, lean_object* v_ref_4251_, lean_object* v_msg_4252_, lean_object* v_declHint_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_4251_, v_msg_4252_, v_declHint_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
return v___x_4263_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4251_ = stack[1].m_obj;
lean_object* v_msg_4252_ = stack[2].m_obj;
lean_object* v_declHint_4253_ = stack[3].m_obj;
lean_object* v___y_4254_ = stack[4].m_obj;
lean_object* v___y_4255_ = stack[5].m_obj;
lean_object* v___y_4256_ = stack[6].m_obj;
lean_object* v___y_4257_ = stack[7].m_obj;
lean_object* v___y_4258_ = stack[8].m_obj;
lean_object* v___y_4259_ = stack[9].m_obj;
lean_object* v___y_4260_ = stack[10].m_obj;
lean_object* v___y_4261_ = stack[11].m_obj;
lean_object* v_res_4264_;
v_res_4264_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(lean_box(0), v_ref_4251_, v_msg_4252_, v_declHint_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
stack->m_obj
 = v_res_4264_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4265_, lean_object* v_ref_4266_, lean_object* v_msg_4267_, lean_object* v_declHint_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(v_00_u03b1_4265_, v_ref_4266_, v_msg_4267_, v_declHint_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v_ref_4266_);
return v_res_4278_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_4279_, lean_object* v_declHint_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_4279_, v_declHint_4280_, v___y_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4279_ = stack[0].m_obj;
lean_object* v_declHint_4280_ = stack[1].m_obj;
lean_object* v___y_4281_ = stack[2].m_obj;
lean_object* v___y_4282_ = stack[3].m_obj;
lean_object* v___y_4283_ = stack[4].m_obj;
lean_object* v___y_4284_ = stack[5].m_obj;
lean_object* v___y_4285_ = stack[6].m_obj;
lean_object* v___y_4286_ = stack[7].m_obj;
lean_object* v___y_4287_ = stack[8].m_obj;
lean_object* v___y_4288_ = stack[9].m_obj;
lean_object* v_res_4291_;
v_res_4291_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_4279_, v_declHint_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
stack->m_obj
 = v_res_4291_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_4292_, lean_object* v_declHint_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_4292_, v_declHint_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
return v_res_4303_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(lean_object* v_00_u03b1_4304_, lean_object* v_ref_4305_, lean_object* v_msg_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_4305_, v_msg_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
return v___x_4316_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4305_ = stack[1].m_obj;
lean_object* v_msg_4306_ = stack[2].m_obj;
lean_object* v___y_4307_ = stack[3].m_obj;
lean_object* v___y_4308_ = stack[4].m_obj;
lean_object* v___y_4309_ = stack[5].m_obj;
lean_object* v___y_4310_ = stack[6].m_obj;
lean_object* v___y_4311_ = stack[7].m_obj;
lean_object* v___y_4312_ = stack[8].m_obj;
lean_object* v___y_4313_ = stack[9].m_obj;
lean_object* v___y_4314_ = stack[10].m_obj;
lean_object* v_res_4317_;
v_res_4317_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(lean_box(0), v_ref_4305_, v_msg_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
stack->m_obj
 = v_res_4317_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b1_4318_, lean_object* v_ref_4319_, lean_object* v_msg_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(v_00_u03b1_4318_, v_ref_4319_, v_msg_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v_ref_4319_);
return v_res_4330_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_toCold_4339_; lean_object* v_options_4340_; lean_object* v___x_4341_; 
v_toCold_4339_ = lean_ctor_get(v___y_4336_, 0);
v_options_4340_ = lean_ctor_get(v_toCold_4339_, 2);
lean_inc_ref(v_options_4340_);
v___x_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4341_, 0, v_options_4340_);
return v___x_4341_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4331_ = stack[0].m_obj;
lean_object* v___y_4332_ = stack[1].m_obj;
lean_object* v___y_4333_ = stack[2].m_obj;
lean_object* v___y_4334_ = stack[3].m_obj;
lean_object* v___y_4335_ = stack[4].m_obj;
lean_object* v___y_4336_ = stack[5].m_obj;
lean_object* v___y_4337_ = stack[6].m_obj;
lean_object* v_res_4342_;
v_res_4342_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
stack->m_obj
 = v_res_4342_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed(lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
return v_res_4351_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v_toCold_4360_; lean_object* v_inheritedTraceOptions_4361_; lean_object* v___x_4362_; 
v_toCold_4360_ = lean_ctor_get(v___y_4357_, 0);
v_inheritedTraceOptions_4361_ = lean_ctor_get(v_toCold_4360_, 11);
lean_inc_ref(v_inheritedTraceOptions_4361_);
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v_inheritedTraceOptions_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4352_ = stack[0].m_obj;
lean_object* v___y_4353_ = stack[1].m_obj;
lean_object* v___y_4354_ = stack[2].m_obj;
lean_object* v___y_4355_ = stack[3].m_obj;
lean_object* v___y_4356_ = stack[4].m_obj;
lean_object* v___y_4357_ = stack[5].m_obj;
lean_object* v___y_4358_ = stack[6].m_obj;
lean_object* v_res_4363_;
v_res_4363_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
stack->m_obj
 = v_res_4363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed(lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
return v_res_4372_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(lean_object* v___x_4373_, lean_object* v___x_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_4373_, v___x_4374_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
return v___x_4383_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4373_ = stack[0].m_obj;
lean_object* v___x_4374_ = stack[1].m_obj;
lean_object* v___y_4375_ = stack[2].m_obj;
lean_object* v___y_4376_ = stack[3].m_obj;
lean_object* v___y_4377_ = stack[4].m_obj;
lean_object* v___y_4378_ = stack[5].m_obj;
lean_object* v___y_4379_ = stack[6].m_obj;
lean_object* v___y_4380_ = stack[7].m_obj;
lean_object* v___y_4381_ = stack[8].m_obj;
lean_object* v_res_4384_;
v_res_4384_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(v___x_4373_, v___x_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
stack->m_obj
 = v_res_4384_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed(lean_object* v___x_4385_, lean_object* v___x_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(v___x_4385_, v___x_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
return v_res_4395_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4398_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_4401_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4400_, v___x_4399_, v___x_4398_);
return v___x_4401_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___f_4405_; lean_object* v___f_4406_; lean_object* v___x_4407_; 
v___x_4404_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4);
v___f_4405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_4407_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4406_, v___f_4405_, v___x_4404_);
return v___x_4407_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4408_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5);
v___x_4409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_4411_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4410_, v___x_4409_, v___x_4408_);
return v___x_4411_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___f_4413_; lean_object* v___f_4414_; lean_object* v___x_4415_; 
v___x_4412_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6);
v___f_4413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_4415_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4414_, v___f_4413_, v___x_4412_);
return v___x_4415_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8(void){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_instMonadEIO___redArg();
return v___x_4416_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4417_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8);
v___x_4418_ = l_StateRefT_x27_instMonad___redArg(v___x_4417_);
return v___x_4418_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14(void){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = l_Lean_Core_instMonadTraceCoreM;
v___x_4424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4425_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_4424_, v___x_4423_);
return v___x_4425_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15(void){
_start:
{
lean_object* v___x_4426_; lean_object* v___f_4427_; lean_object* v___x_4428_; 
v___x_4426_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14);
v___f_4427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4428_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4427_, v___x_4426_);
return v___x_4428_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16(void){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4429_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15);
v___x_4430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4431_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_4430_, v___x_4429_);
return v___x_4431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17(void){
_start:
{
lean_object* v___x_4432_; lean_object* v___f_4433_; lean_object* v___x_4434_; 
v___x_4432_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16);
v___f_4433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4434_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4433_, v___x_4432_);
return v___x_4434_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18(void){
_start:
{
lean_object* v___x_4435_; lean_object* v___f_4436_; lean_object* v___x_4437_; 
v___x_4435_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17);
v___f_4436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4437_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4436_, v___x_4435_);
return v___x_4437_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19(void){
_start:
{
lean_object* v___x_4438_; lean_object* v___f_4439_; lean_object* v___x_4440_; 
v___x_4438_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18);
v___f_4439_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___x_4440_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4439_, v___x_4438_);
return v___x_4440_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___f_4445_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4444_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4445_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4445_, 0, v___x_4444_);
lean_closure_set(v___f_4445_, 1, v___x_4443_);
return v___f_4445_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23(void){
_start:
{
lean_object* v___f_4446_; lean_object* v___f_4447_; lean_object* v___f_4448_; 
v___f_4446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4447_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22);
v___f_4448_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4448_, 0, v___f_4447_);
lean_closure_set(v___f_4448_, 1, v___f_4446_);
return v___f_4448_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24(void){
_start:
{
lean_object* v___f_4449_; lean_object* v___f_4450_; lean_object* v___f_4451_; 
v___f_4449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4450_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23);
v___f_4451_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4451_, 0, v___f_4450_);
lean_closure_set(v___f_4451_, 1, v___f_4449_);
return v___f_4451_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25(void){
_start:
{
lean_object* v___f_4452_; lean_object* v___f_4453_; lean_object* v___f_4454_; 
v___f_4452_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___f_4453_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24);
v___f_4454_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4454_, 0, v___f_4453_);
lean_closure_set(v___f_4454_, 1, v___f_4452_);
return v___f_4454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28(void){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_4459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27));
v___x_4460_ = l_Lean_Name_append(v___x_4459_, v___x_4458_);
return v___x_4460_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30(void){
_start:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29));
v___x_4463_ = l_Lean_stringToMessageData(v___x_4462_);
return v___x_4463_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32(void){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31));
v___x_4466_ = l_Lean_stringToMessageData(v___x_4465_);
return v___x_4466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34(void){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33));
v___x_4469_ = l_Lean_stringToMessageData(v___x_4468_);
return v___x_4469_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36(void){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__35));
v___x_4472_ = l_Lean_stringToMessageData(v___x_4471_);
return v___x_4472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38(void){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__37));
v___x_4475_ = l_Lean_stringToMessageData(v___x_4474_);
return v___x_4475_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(lean_object* v_xs_4476_, lean_object* v_k_4477_, lean_object* v_runInBase_4478_, lean_object* v_i_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v___y_4488_; lean_object* v___y_4489_; uint8_t v___y_4490_; lean_object* v___y_4495_; lean_object* v_a_4496_; lean_object* v_a_4500_; lean_object* v___y_4503_; lean_object* v___x_4505_; lean_object* v_toMonadRef_4506_; lean_object* v___x_4507_; lean_object* v_toApplicative_4508_; lean_object* v_toFunctor_4509_; lean_object* v_toSeq_4510_; lean_object* v_toSeqLeft_4511_; lean_object* v_toSeqRight_4512_; lean_object* v___f_4513_; lean_object* v___f_4514_; lean_object* v___f_4515_; lean_object* v___f_4516_; lean_object* v___x_4517_; lean_object* v___f_4518_; lean_object* v___f_4519_; lean_object* v___f_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v_toApplicative_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4622_; 
v___x_4505_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7);
v_toMonadRef_4506_ = lean_ctor_get(v___x_4505_, 0);
v___x_4507_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9);
v_toApplicative_4508_ = lean_ctor_get(v___x_4507_, 0);
v_toFunctor_4509_ = lean_ctor_get(v_toApplicative_4508_, 0);
v_toSeq_4510_ = lean_ctor_get(v_toApplicative_4508_, 2);
v_toSeqLeft_4511_ = lean_ctor_get(v_toApplicative_4508_, 3);
v_toSeqRight_4512_ = lean_ctor_get(v_toApplicative_4508_, 4);
v___f_4513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__10));
v___f_4514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__11));
lean_inc_ref_n(v_toFunctor_4509_, 2);
v___f_4515_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4515_, 0, v_toFunctor_4509_);
v___f_4516_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4516_, 0, v_toFunctor_4509_);
v___x_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___f_4515_);
lean_ctor_set(v___x_4517_, 1, v___f_4516_);
lean_inc(v_toSeqRight_4512_);
v___f_4518_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4518_, 0, v_toSeqRight_4512_);
lean_inc(v_toSeqLeft_4511_);
v___f_4519_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4519_, 0, v_toSeqLeft_4511_);
lean_inc(v_toSeq_4510_);
v___f_4520_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4520_, 0, v_toSeq_4510_);
v___x_4521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4517_);
lean_ctor_set(v___x_4521_, 1, v___f_4513_);
lean_ctor_set(v___x_4521_, 2, v___f_4520_);
lean_ctor_set(v___x_4521_, 3, v___f_4519_);
lean_ctor_set(v___x_4521_, 4, v___f_4518_);
v___x_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v___f_4514_);
v___x_4523_ = l_StateRefT_x27_instMonad___redArg(v___x_4522_);
v_toApplicative_4524_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4622_ == 0)
{
lean_object* v_unused_4623_; 
v_unused_4623_ = lean_ctor_get(v___x_4523_, 1);
lean_dec(v_unused_4623_);
v___x_4526_ = v___x_4523_;
v_isShared_4527_ = v_isSharedCheck_4622_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_toApplicative_4524_);
lean_dec(v___x_4523_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4622_;
goto v_resetjp_4525_;
}
v___jp_4487_:
{
if (v___y_4490_ == 0)
{
if (lean_obj_tag(v___y_4489_) == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; 
lean_dec_ref_known(v___y_4489_, 2);
lean_dec_ref(v___y_4488_);
v___x_4491_ = lean_unsigned_to_nat(1u);
v___x_4492_ = lean_nat_add(v_i_4479_, v___x_4491_);
lean_dec(v_i_4479_);
v_i_4479_ = v___x_4492_;
goto _start;
}
else
{
lean_dec_ref_known(v___y_4489_, 2);
lean_dec(v_i_4479_);
lean_dec_ref(v_runInBase_4478_);
lean_dec(v_k_4477_);
return v___y_4488_;
}
}
else
{
lean_dec_ref(v___y_4489_);
lean_dec(v_i_4479_);
lean_dec_ref(v_runInBase_4478_);
lean_dec(v_k_4477_);
return v___y_4488_;
}
}
v___jp_4494_:
{
uint8_t v___x_4497_; 
v___x_4497_ = l_Lean_Exception_isInterrupt(v_a_4496_);
if (v___x_4497_ == 0)
{
uint8_t v___x_4498_; 
lean_inc_ref(v_a_4496_);
v___x_4498_ = l_Lean_Exception_isRuntime(v_a_4496_);
v___y_4488_ = v___y_4495_;
v___y_4489_ = v_a_4496_;
v___y_4490_ = v___x_4498_;
goto v___jp_4487_;
}
else
{
v___y_4488_ = v___y_4495_;
v___y_4489_ = v_a_4496_;
v___y_4490_ = v___x_4497_;
goto v___jp_4487_;
}
}
v___jp_4499_:
{
lean_object* v___x_4501_; 
lean_inc_ref(v_a_4500_);
v___x_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4501_, 0, v_a_4500_);
v___y_4495_ = v___x_4501_;
v_a_4496_ = v_a_4500_;
goto v___jp_4494_;
}
v___jp_4502_:
{
if (lean_obj_tag(v___y_4503_) == 0)
{
lean_dec(v_i_4479_);
lean_dec_ref(v_runInBase_4478_);
lean_dec(v_k_4477_);
return v___y_4503_;
}
else
{
lean_object* v_a_4504_; 
v_a_4504_ = lean_ctor_get(v___y_4503_, 0);
lean_inc(v_a_4504_);
v___y_4495_ = v___y_4503_;
v_a_4496_ = v_a_4504_;
goto v___jp_4494_;
}
}
v_resetjp_4525_:
{
lean_object* v_toFunctor_4528_; lean_object* v_toSeq_4529_; lean_object* v_toSeqLeft_4530_; lean_object* v_toSeqRight_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4620_; 
v_toFunctor_4528_ = lean_ctor_get(v_toApplicative_4524_, 0);
v_toSeq_4529_ = lean_ctor_get(v_toApplicative_4524_, 2);
v_toSeqLeft_4530_ = lean_ctor_get(v_toApplicative_4524_, 3);
v_toSeqRight_4531_ = lean_ctor_get(v_toApplicative_4524_, 4);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_toApplicative_4524_);
if (v_isSharedCheck_4620_ == 0)
{
lean_object* v_unused_4621_; 
v_unused_4621_ = lean_ctor_get(v_toApplicative_4524_, 1);
lean_dec(v_unused_4621_);
v___x_4533_ = v_toApplicative_4524_;
v_isShared_4534_ = v_isSharedCheck_4620_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_toSeqRight_4531_);
lean_inc(v_toSeqLeft_4530_);
lean_inc(v_toSeq_4529_);
lean_inc(v_toFunctor_4528_);
lean_dec(v_toApplicative_4524_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4620_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___f_4535_; lean_object* v___f_4536_; lean_object* v___f_4537_; lean_object* v___f_4538_; lean_object* v___x_4539_; lean_object* v___f_4540_; lean_object* v___f_4541_; lean_object* v___f_4542_; lean_object* v___x_4544_; 
v___f_4535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__12));
v___f_4536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__13));
lean_inc_ref(v_toFunctor_4528_);
v___f_4537_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4537_, 0, v_toFunctor_4528_);
v___f_4538_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4538_, 0, v_toFunctor_4528_);
v___x_4539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___f_4537_);
lean_ctor_set(v___x_4539_, 1, v___f_4538_);
v___f_4540_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4540_, 0, v_toSeqRight_4531_);
v___f_4541_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4541_, 0, v_toSeqLeft_4530_);
v___f_4542_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4542_, 0, v_toSeq_4529_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v___f_4540_);
lean_ctor_set(v___x_4533_, 3, v___f_4541_);
lean_ctor_set(v___x_4533_, 2, v___f_4542_);
lean_ctor_set(v___x_4533_, 1, v___f_4535_);
lean_ctor_set(v___x_4533_, 0, v___x_4539_);
v___x_4544_ = v___x_4533_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4539_);
lean_ctor_set(v_reuseFailAlloc_4619_, 1, v___f_4535_);
lean_ctor_set(v_reuseFailAlloc_4619_, 2, v___f_4542_);
lean_ctor_set(v_reuseFailAlloc_4619_, 3, v___f_4541_);
lean_ctor_set(v_reuseFailAlloc_4619_, 4, v___f_4540_);
v___x_4544_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4546_; 
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 1, v___f_4536_);
lean_ctor_set(v___x_4526_, 0, v___x_4544_);
v___x_4546_ = v___x_4526_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4544_);
lean_ctor_set(v_reuseFailAlloc_4618_, 1, v___f_4536_);
v___x_4546_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4547_ = l_StateRefT_x27_instMonad___redArg(v___x_4546_);
v___x_4548_ = l_ReaderT_instMonad___redArg(v___x_4547_);
v___x_4549_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19);
v___x_4550_ = lean_array_get_size(v_xs_4476_);
v___x_4551_ = lean_nat_dec_lt(v_i_4479_, v___x_4550_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
lean_dec_ref(v___x_4548_);
lean_dec(v_i_4479_);
lean_inc(v_a_4485_);
lean_inc_ref(v_a_4484_);
lean_inc(v_a_4483_);
lean_inc_ref(v_a_4482_);
lean_inc(v_a_4481_);
lean_inc_ref(v_a_4480_);
v___x_4552_ = lean_apply_9(v_runInBase_4478_, lean_box(0), v_k_4477_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, lean_box(0));
return v___x_4552_;
}
else
{
lean_object* v___f_4553_; lean_object* v___f_4554_; lean_object* v___f_4555_; lean_object* v_x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___f_4559_; lean_object* v___x_4560_; 
v___f_4553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20));
v___f_4554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21));
v___f_4555_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25);
v_x_4556_ = lean_array_fget_borrowed(v_xs_4476_, v_i_4479_);
v___x_4557_ = l_Lean_Expr_fvarId_x21(v_x_4556_);
v___x_4558_ = lean_unsigned_to_nat(100u);
v___f_4559_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed), 10, 2);
lean_closure_set(v___f_4559_, 0, v___x_4557_);
lean_closure_set(v___f_4559_, 1, v___x_4558_);
v___x_4560_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4559_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref_known(v___x_4560_, 1);
v___x_4565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_4566_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4554_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4568_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref_known(v___x_4566_, 1);
v___x_4568_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4553_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4569_; uint8_t v_hasTrace_4570_; 
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4569_);
lean_dec_ref_known(v___x_4568_, 1);
v_hasTrace_4570_ = lean_ctor_get_uint8(v_a_4569_, sizeof(void*)*1);
if (v_hasTrace_4570_ == 0)
{
lean_dec(v_a_4569_);
lean_dec(v_a_4567_);
lean_dec_ref(v___x_4548_);
goto v___jp_4562_;
}
else
{
lean_object* v___x_4571_; uint8_t v___x_4572_; 
v___x_4571_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28);
v___x_4572_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_a_4567_, v_a_4569_, v___x_4571_);
lean_dec(v_a_4569_);
lean_dec(v_a_4567_);
if (v___x_4572_ == 0)
{
lean_dec_ref(v___x_4548_);
goto v___jp_4562_;
}
else
{
lean_object* v_proof_4573_; lean_object* v___x_4574_; lean_object* v___y_4576_; 
v_proof_4573_ = lean_ctor_get(v_a_4561_, 2);
v___x_4574_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30);
switch(lean_obj_tag(v_proof_4573_))
{
case 0:
{
lean_object* v_declName_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v_declName_4590_ = lean_ctor_get(v_proof_4573_, 0);
v___x_4591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32);
lean_inc(v_declName_4590_);
v___x_4592_ = l_Lean_MessageData_ofName(v_declName_4590_);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___y_4576_ = v___x_4593_;
goto v___jp_4575_;
}
case 1:
{
lean_object* v_fvarId_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v_fvarId_4594_ = lean_ctor_get(v_proof_4573_, 0);
v___x_4595_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34);
lean_inc(v_fvarId_4594_);
v___x_4596_ = l_Lean_mkFVar(v_fvarId_4594_);
v___x_4597_ = l_Lean_MessageData_ofExpr(v___x_4596_);
v___x_4598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4595_);
lean_ctor_set(v___x_4598_, 1, v___x_4597_);
v___y_4576_ = v___x_4598_;
goto v___jp_4575_;
}
default: 
{
lean_object* v_ref_4599_; lean_object* v_proof_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v_ref_4599_ = lean_ctor_get(v_proof_4573_, 1);
v_proof_4600_ = lean_ctor_get(v_proof_4573_, 2);
v___x_4601_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36);
lean_inc(v_ref_4599_);
v___x_4602_ = l_Lean_MessageData_ofSyntax(v_ref_4599_);
v___x_4603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4601_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
v___x_4604_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38);
v___x_4605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4603_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
lean_inc_ref(v_proof_4600_);
v___x_4606_ = l_Lean_MessageData_ofExpr(v_proof_4600_);
v___x_4607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4605_);
lean_ctor_set(v___x_4607_, 1, v___x_4606_);
v___y_4576_ = v___x_4607_;
goto v___jp_4575_;
}
}
v___jp_4575_:
{
lean_object* v___x_4577_; lean_object* v___x_5564__overap_4578_; lean_object* v___x_4579_; 
v___x_4577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4574_);
lean_ctor_set(v___x_4577_, 1, v___y_4576_);
lean_inc_ref(v_toMonadRef_4506_);
v___x_5564__overap_4578_ = l_Lean_addTrace___redArg(v___x_4548_, v___x_4549_, v_toMonadRef_4506_, v___f_4555_, v___x_4565_, v___x_4577_);
lean_inc(v_a_4485_);
lean_inc_ref(v_a_4484_);
lean_inc(v_a_4483_);
lean_inc_ref(v_a_4482_);
lean_inc(v_a_4481_);
lean_inc_ref(v_a_4480_);
v___x_4579_ = lean_apply_7(v___x_5564__overap_4578_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, lean_box(0));
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4581_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
lean_inc_ref(v_runInBase_4478_);
lean_inc(v_k_4477_);
v___x_4581_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4479_, v_a_4561_, v_xs_4476_, v_k_4477_, v_runInBase_4478_, v_a_4580_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
v___y_4503_ = v___x_4581_;
goto v___jp_4502_;
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
lean_dec(v_a_4561_);
v_a_4582_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4579_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4579_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
lean_inc(v_a_4582_);
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
v___y_4495_ = v___x_4587_;
v_a_4496_ = v_a_4582_;
goto v___jp_4494_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4608_; 
lean_dec(v_a_4567_);
lean_dec(v_a_4561_);
lean_dec_ref(v___x_4548_);
v_a_4608_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v___x_4568_, 1);
v_a_4500_ = v_a_4608_;
goto v___jp_4499_;
}
}
else
{
lean_object* v_a_4609_; 
lean_dec(v_a_4561_);
lean_dec_ref(v___x_4548_);
v_a_4609_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4566_, 1);
v_a_4500_ = v_a_4609_;
goto v___jp_4499_;
}
v___jp_4562_:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = lean_box(0);
lean_inc_ref(v_runInBase_4478_);
lean_inc(v_k_4477_);
v___x_4564_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4479_, v_a_4561_, v_xs_4476_, v_k_4477_, v_runInBase_4478_, v___x_4563_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
v___y_4503_ = v___x_4564_;
goto v___jp_4502_;
}
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_dec_ref(v___x_4548_);
v_a_4610_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4560_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4560_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
lean_inc(v_a_4610_);
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
v___y_4495_ = v___x_4615_;
v_a_4496_ = v_a_4610_;
goto v___jp_4494_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4476_ = stack[0].m_obj;
lean_object* v_k_4477_ = stack[1].m_obj;
lean_object* v_runInBase_4478_ = stack[2].m_obj;
lean_object* v_i_4479_ = stack[3].m_obj;
lean_object* v_a_4480_ = stack[4].m_obj;
lean_object* v_a_4481_ = stack[5].m_obj;
lean_object* v_a_4482_ = stack[6].m_obj;
lean_object* v_a_4483_ = stack[7].m_obj;
lean_object* v_a_4484_ = stack[8].m_obj;
lean_object* v_a_4485_ = stack[9].m_obj;
lean_object* v_res_4624_;
v_res_4624_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4476_, v_k_4477_, v_runInBase_4478_, v_i_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_);
stack->m_obj
 = v_res_4624_;
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(lean_object* v_i_4625_, lean_object* v_a_4626_, lean_object* v_xs_4627_, lean_object* v_k_4628_, lean_object* v_runInBase_4629_, lean_object* v_____r_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v_config_4638_; lean_object* v_specThms_4639_; lean_object* v_simpCtx_4640_; lean_object* v_simprocs_4641_; lean_object* v_jps_4642_; lean_object* v_initialCtxSize_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v_config_4638_ = lean_ctor_get(v___y_4631_, 0);
v_specThms_4639_ = lean_ctor_get(v___y_4631_, 1);
v_simpCtx_4640_ = lean_ctor_get(v___y_4631_, 2);
v_simprocs_4641_ = lean_ctor_get(v___y_4631_, 3);
v_jps_4642_ = lean_ctor_get(v___y_4631_, 4);
v_initialCtxSize_4643_ = lean_ctor_get(v___y_4631_, 5);
v___x_4644_ = lean_unsigned_to_nat(1u);
v___x_4645_ = lean_nat_add(v_i_4625_, v___x_4644_);
lean_inc_ref(v_specThms_4639_);
v___x_4646_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_specThms_4639_, v_a_4626_);
lean_inc(v_initialCtxSize_4643_);
lean_inc(v_jps_4642_);
lean_inc_ref(v_simprocs_4641_);
lean_inc_ref(v_simpCtx_4640_);
lean_inc_ref(v_config_4638_);
v___x_4647_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4647_, 0, v_config_4638_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
lean_ctor_set(v___x_4647_, 2, v_simpCtx_4640_);
lean_ctor_set(v___x_4647_, 3, v_simprocs_4641_);
lean_ctor_set(v___x_4647_, 4, v_jps_4642_);
lean_ctor_set(v___x_4647_, 5, v_initialCtxSize_4643_);
v___x_4648_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4627_, v_k_4628_, v_runInBase_4629_, v___x_4645_, v___x_4647_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
lean_dec_ref_known(v___x_4647_, 6);
return v___x_4648_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_4625_ = stack[0].m_obj;
lean_object* v_a_4626_ = stack[1].m_obj;
lean_object* v_xs_4627_ = stack[2].m_obj;
lean_object* v_k_4628_ = stack[3].m_obj;
lean_object* v_runInBase_4629_ = stack[4].m_obj;
lean_object* v_____r_4630_ = stack[5].m_obj;
lean_object* v___y_4631_ = stack[6].m_obj;
lean_object* v___y_4632_ = stack[7].m_obj;
lean_object* v___y_4633_ = stack[8].m_obj;
lean_object* v___y_4634_ = stack[9].m_obj;
lean_object* v___y_4635_ = stack[10].m_obj;
lean_object* v___y_4636_ = stack[11].m_obj;
lean_object* v_res_4649_;
v_res_4649_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4625_, v_a_4626_, v_xs_4627_, v_k_4628_, v_runInBase_4629_, v_____r_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
stack->m_obj
 = v_res_4649_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3___boxed(lean_object* v_i_4650_, lean_object* v_a_4651_, lean_object* v_xs_4652_, lean_object* v_k_4653_, lean_object* v_runInBase_4654_, lean_object* v_____r_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4650_, v_a_4651_, v_xs_4652_, v_k_4653_, v_runInBase_4654_, v_____r_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec_ref(v_xs_4652_);
lean_dec(v_i_4650_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___boxed(lean_object* v_xs_4664_, lean_object* v_k_4665_, lean_object* v_runInBase_4666_, lean_object* v_i_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4664_, v_k_4665_, v_runInBase_4666_, v_i_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
lean_dec(v_a_4669_);
lean_dec_ref(v_a_4668_);
lean_dec_ref(v_xs_4664_);
return v_res_4675_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(lean_object* v_m_4676_, lean_object* v_00_u03b1_4677_, lean_object* v_inst_4678_, lean_object* v_xs_4679_, lean_object* v_k_4680_, lean_object* v_runInBase_4681_, lean_object* v_i_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; 
v___x_4690_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4679_, v_k_4680_, v_runInBase_4681_, v_i_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
return v___x_4690_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4678_ = stack[2].m_obj;
lean_object* v_xs_4679_ = stack[3].m_obj;
lean_object* v_k_4680_ = stack[4].m_obj;
lean_object* v_runInBase_4681_ = stack[5].m_obj;
lean_object* v_i_4682_ = stack[6].m_obj;
lean_object* v_a_4683_ = stack[7].m_obj;
lean_object* v_a_4684_ = stack[8].m_obj;
lean_object* v_a_4685_ = stack[9].m_obj;
lean_object* v_a_4686_ = stack[10].m_obj;
lean_object* v_a_4687_ = stack[11].m_obj;
lean_object* v_a_4688_ = stack[12].m_obj;
lean_object* v_res_4691_;
v_res_4691_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(lean_box(0), lean_box(0), v_inst_4678_, v_xs_4679_, v_k_4680_, v_runInBase_4681_, v_i_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
stack->m_obj
 = v_res_4691_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___boxed(lean_object* v_m_4692_, lean_object* v_00_u03b1_4693_, lean_object* v_inst_4694_, lean_object* v_xs_4695_, lean_object* v_k_4696_, lean_object* v_runInBase_4697_, lean_object* v_i_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(v_m_4692_, v_00_u03b1_4693_, v_inst_4694_, v_xs_4695_, v_k_4696_, v_runInBase_4697_, v_i_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec_ref(v_xs_4695_);
lean_dec_ref(v_inst_4694_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter___redArg(lean_object* v_ex_4707_, lean_object* v_h__1_4708_, lean_object* v_h__2_4709_){
_start:
{
if (lean_obj_tag(v_ex_4707_) == 0)
{
lean_object* v_ref_4710_; lean_object* v_msg_4711_; lean_object* v___x_4712_; 
lean_dec(v_h__1_4708_);
v_ref_4710_ = lean_ctor_get(v_ex_4707_, 0);
lean_inc(v_ref_4710_);
v_msg_4711_ = lean_ctor_get(v_ex_4707_, 1);
lean_inc_ref(v_msg_4711_);
lean_dec_ref_known(v_ex_4707_, 2);
v___x_4712_ = lean_apply_2(v_h__2_4709_, v_ref_4710_, v_msg_4711_);
return v___x_4712_;
}
else
{
lean_object* v_id_4713_; lean_object* v_extra_4714_; lean_object* v___x_4715_; 
lean_dec(v_h__2_4709_);
v_id_4713_ = lean_ctor_get(v_ex_4707_, 0);
lean_inc(v_id_4713_);
v_extra_4714_ = lean_ctor_get(v_ex_4707_, 1);
lean_inc(v_extra_4714_);
lean_dec_ref_known(v_ex_4707_, 2);
v___x_4715_ = lean_apply_2(v_h__1_4708_, v_id_4713_, v_extra_4714_);
return v___x_4715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter(lean_object* v_motive_4716_, lean_object* v_ex_4717_, lean_object* v_h__1_4718_, lean_object* v_h__2_4719_){
_start:
{
if (lean_obj_tag(v_ex_4717_) == 0)
{
lean_object* v_ref_4720_; lean_object* v_msg_4721_; lean_object* v___x_4722_; 
lean_dec(v_h__1_4718_);
v_ref_4720_ = lean_ctor_get(v_ex_4717_, 0);
lean_inc(v_ref_4720_);
v_msg_4721_ = lean_ctor_get(v_ex_4717_, 1);
lean_inc_ref(v_msg_4721_);
lean_dec_ref_known(v_ex_4717_, 2);
v___x_4722_ = lean_apply_2(v_h__2_4719_, v_ref_4720_, v_msg_4721_);
return v___x_4722_;
}
else
{
lean_object* v_id_4723_; lean_object* v_extra_4724_; lean_object* v___x_4725_; 
lean_dec(v_h__2_4719_);
v_id_4723_ = lean_ctor_get(v_ex_4717_, 0);
lean_inc(v_id_4723_);
v_extra_4724_ = lean_ctor_get(v_ex_4717_, 1);
lean_inc(v_extra_4724_);
lean_dec_ref_known(v_ex_4717_, 2);
v___x_4725_ = lean_apply_2(v_h__1_4718_, v_id_4723_, v_extra_4724_);
return v___x_4725_;
}
}
}
lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(lean_object* v_xs_4726_, lean_object* v_k_4727_, lean_object* v_runInBase_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_unsigned_to_nat(0u);
v___x_4737_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4726_, v_k_4727_, v_runInBase_4728_, v___x_4736_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
return v___x_4737_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4726_ = stack[0].m_obj;
lean_object* v_k_4727_ = stack[1].m_obj;
lean_object* v_runInBase_4728_ = stack[2].m_obj;
lean_object* v___y_4729_ = stack[3].m_obj;
lean_object* v___y_4730_ = stack[4].m_obj;
lean_object* v___y_4731_ = stack[5].m_obj;
lean_object* v___y_4732_ = stack[6].m_obj;
lean_object* v___y_4733_ = stack[7].m_obj;
lean_object* v___y_4734_ = stack[8].m_obj;
lean_object* v_res_4738_;
v_res_4738_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(v_xs_4726_, v_k_4727_, v_runInBase_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
stack->m_obj
 = v_res_4738_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed(lean_object* v_xs_4739_, lean_object* v_k_4740_, lean_object* v_runInBase_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(v_xs_4739_, v_k_4740_, v_runInBase_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec_ref(v_xs_4739_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(lean_object* v_inst_4750_, lean_object* v_inst_4751_, lean_object* v_xs_4752_, lean_object* v_k_4753_){
_start:
{
lean_object* v_toBind_4754_; lean_object* v_liftWith_4755_; lean_object* v_restoreM_4756_; lean_object* v___f_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v_toBind_4754_ = lean_ctor_get(v_inst_4750_, 1);
lean_inc(v_toBind_4754_);
lean_dec_ref(v_inst_4750_);
v_liftWith_4755_ = lean_ctor_get(v_inst_4751_, 0);
lean_inc(v_liftWith_4755_);
v_restoreM_4756_ = lean_ctor_get(v_inst_4751_, 1);
lean_inc(v_restoreM_4756_);
lean_dec_ref(v_inst_4751_);
v___f_4757_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4757_, 0, v_xs_4752_);
lean_closure_set(v___f_4757_, 1, v_k_4753_);
v___x_4758_ = lean_apply_2(v_liftWith_4755_, lean_box(0), v___f_4757_);
v___x_4759_ = lean_apply_1(v_restoreM_4756_, lean_box(0));
v___x_4760_ = lean_apply_4(v_toBind_4754_, lean_box(0), lean_box(0), v___x_4758_, v___x_4759_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs(lean_object* v_m_4761_, lean_object* v_00_u03b1_4762_, lean_object* v_inst_4763_, lean_object* v_inst_4764_, lean_object* v_xs_4765_, lean_object* v_k_4766_){
_start:
{
lean_object* v___x_4767_; 
v___x_4767_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(v_inst_4763_, v_inst_4764_, v_xs_4765_, v_k_4766_);
return v___x_4767_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_ConfigEval(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Do_mvcgen_warning = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Do_mvcgen_warning);
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig = _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Attr(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_Elab_ConfigEval(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ConfigEval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
