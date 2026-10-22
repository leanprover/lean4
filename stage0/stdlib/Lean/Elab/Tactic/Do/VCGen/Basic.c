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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2____boxed(lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_();
return v_res_96_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(4153898153u);
v___x_105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_106_ = l_Lean_Name_num___override(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_108_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_109_ = l_Lean_Name_str___override(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_111_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_112_ = l_Lean_Name_str___override(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(2u);
v___x_114_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_115_ = l_Lean_Name_num___override(v___x_114_, v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_));
v___x_118_ = 0;
v___x_119_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_);
v___x_120_ = l_Lean_registerTraceClass(v___x_117_, v___x_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2____boxed(lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_4153898153____hygCtx___hyg_2_();
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(lean_object* v_name_123_, lean_object* v_decl_124_, lean_object* v_ref_125_){
_start:
{
lean_object* v_defValue_127_; lean_object* v_descr_128_; lean_object* v_deprecation_x3f_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_defValue_127_ = lean_ctor_get(v_decl_124_, 0);
v_descr_128_ = lean_ctor_get(v_decl_124_, 1);
v_deprecation_x3f_129_ = lean_ctor_get(v_decl_124_, 2);
v___x_130_ = lean_alloc_ctor(1, 0, 1);
v___x_131_ = lean_unbox(v_defValue_127_);
lean_ctor_set_uint8(v___x_130_, 0, v___x_131_);
lean_inc(v_deprecation_x3f_129_);
lean_inc_ref(v_descr_128_);
lean_inc_n(v_name_123_, 2);
v___x_132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_132_, 0, v_name_123_);
lean_ctor_set(v___x_132_, 1, v_ref_125_);
lean_ctor_set(v___x_132_, 2, v___x_130_);
lean_ctor_set(v___x_132_, 3, v_descr_128_);
lean_ctor_set(v___x_132_, 4, v_deprecation_x3f_129_);
v___x_133_ = lean_register_option(v_name_123_, v___x_132_);
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
lean_inc(v_defValue_127_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_name_123_);
lean_ctor_set(v___x_137_, 1, v_defValue_127_);
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
lean_dec(v_name_123_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_151_, lean_object* v_decl_152_, lean_object* v_ref_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(v_name_151_, v_decl_152_, v_ref_153_);
lean_dec_ref(v_decl_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_));
v___x_186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_));
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_));
v___x_188_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4__spec__0(v___x_185_, v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4____boxed(lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1636623291____hygCtx___hyg_4_();
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl(lean_object* v_x_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_tag_nat(v_x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl___boxed(lean_object* v_x_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___impl(v_x_193_);
lean_dec(v_x_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(lean_object* v_t_195_, lean_object* v_k_196_){
_start:
{
if (lean_obj_tag(v_t_195_) == 0)
{
lean_object* v_n_197_; lean_object* v___x_198_; 
v_n_197_ = lean_ctor_get(v_t_195_, 0);
lean_inc(v_n_197_);
lean_dec_ref_known(v_t_195_, 1);
v___x_198_ = lean_apply_1(v_k_196_, v_n_197_);
return v___x_198_;
}
else
{
return v_k_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim(lean_object* v_motive_199_, lean_object* v_ctorIdx_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_k_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_201_, v_k_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___boxed(lean_object* v_motive_205_, lean_object* v_ctorIdx_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim(v_motive_205_, v_ctorIdx_206_, v_t_207_, v_h_208_, v_k_209_);
lean_dec(v_ctorIdx_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim___redArg(lean_object* v_t_211_, lean_object* v_limited_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_211_, v_limited_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_limited_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_215_, v_limited_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim___redArg(lean_object* v_t_219_, lean_object* v_unlimited_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_219_, v_unlimited_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim(lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_unlimited_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_223_, v_unlimited_225_);
return v___x_226_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_n_229_; lean_object* v_n_230_; uint8_t v___x_231_; 
v_n_229_ = lean_ctor_get(v_x_227_, 0);
v_n_230_ = lean_ctor_get(v_x_228_, 0);
v___x_231_ = lean_nat_dec_eq(v_n_229_, v_n_230_);
return v___x_231_;
}
else
{
uint8_t v___x_232_; 
v___x_232_ = 0;
return v___x_232_;
}
}
else
{
if (lean_obj_tag(v_x_228_) == 0)
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
else
{
uint8_t v___x_234_; 
v___x_234_ = 1;
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq___boxed(lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
uint8_t v_res_237_; lean_object* v_r_238_; 
v_res_237_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_235_, v_x_236_);
lean_dec(v_x_236_);
lean_dec(v_x_235_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_239_, v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel___boxed(lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel(v_x_242_, v_x_243_);
lean_dec(v_x_243_);
lean_dec(v_x_242_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_box(0);
v___x_247_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(lean_object* v_msgData_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v_env_275_; uint8_t v___x_276_; lean_object* v_env_277_; lean_object* v___x_278_; lean_object* v_toCold_279_; lean_object* v_mctx_280_; lean_object* v_lctx_281_; lean_object* v_options_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_274_ = lean_st_ref_get(v___y_272_);
v_env_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc_ref(v_env_275_);
lean_dec(v___x_274_);
v___x_276_ = 0;
v_env_277_ = l_Lean_Environment_setRecordingDeps(v_env_275_, v___x_276_);
v___x_278_ = lean_st_ref_get(v___y_270_);
v_toCold_279_ = lean_ctor_get(v___y_271_, 0);
v_mctx_280_ = lean_ctor_get(v___x_278_, 0);
lean_inc_ref(v_mctx_280_);
lean_dec(v___x_278_);
v_lctx_281_ = lean_ctor_get(v___y_269_, 2);
v_options_282_ = lean_ctor_get(v_toCold_279_, 2);
lean_inc_ref(v_options_282_);
lean_inc_ref(v_lctx_281_);
v___x_283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_283_, 0, v_env_277_);
lean_ctor_set(v___x_283_, 1, v_mctx_280_);
lean_ctor_set(v___x_283_, 2, v_lctx_281_);
lean_ctor_set(v___x_283_, 3, v_options_282_);
v___x_284_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_msgData_268_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msgData_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_ref_299_; lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_309_; 
v_ref_299_ = lean_ctor_get(v___y_296_, 2);
v___x_300_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_309_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_309_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_307_; 
lean_inc(v_ref_299_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_ref_299_);
lean_ctor_set(v___x_305_, 1, v_a_301_);
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 1);
lean_ctor_set(v___x_303_, 0, v___x_305_);
v___x_307_ = v___x_303_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_316_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_320_ = l_Lean_stringToMessageData(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(lean_object* v___x_321_, lean_object* v___x_322_, lean_object* v_ctor_323_, lean_object* v_args_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_444_ = lean_string_dec_eq(v_ctor_323_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec_ref(v___x_322_);
v___x_445_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_array_get_size(v_args_324_);
v___x_447_ = lean_unsigned_to_nat(8u);
v___x_448_ = lean_nat_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v___x_322_);
v___x_449_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_450_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_449_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
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
goto v___jp_330_;
}
}
v___jp_330_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_331_);
lean_inc(v___x_332_);
v___x_333_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_332_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_335_);
lean_inc(v___x_336_);
v___x_337_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_336_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = lean_unsigned_to_nat(2u);
v___x_340_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_339_);
lean_inc(v___x_340_);
v___x_341_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_340_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = lean_unsigned_to_nat(3u);
v___x_344_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_343_);
lean_inc(v___x_344_);
v___x_345_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_344_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v_evalExpr_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v_evalExpr_347_ = lean_ctor_get(v___x_322_, 0);
lean_inc_ref(v_evalExpr_347_);
lean_dec_ref(v___x_322_);
v___x_348_ = lean_unsigned_to_nat(4u);
v___x_349_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_348_);
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v___x_349_);
v___x_350_ = lean_apply_6(v_evalExpr_347_, v___x_349_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, lean_box(0));
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v___x_352_ = lean_unsigned_to_nat(5u);
v___x_353_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_352_);
lean_inc(v___x_353_);
v___x_354_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_353_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = lean_unsigned_to_nat(6u);
v___x_357_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_356_);
lean_inc(v___x_357_);
v___x_358_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_357_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = lean_unsigned_to_nat(7u);
v___x_361_ = lean_array_get_borrowed(v___x_321_, v_args_324_, v___x_360_);
lean_inc(v___x_361_);
v___x_362_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_361_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_378_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_378_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_378_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_378_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; uint8_t v___x_368_; uint8_t v___x_369_; uint8_t v___x_370_; uint8_t v___x_371_; uint8_t v___x_372_; uint8_t v___x_373_; uint8_t v___x_374_; lean_object* v___x_376_; 
v___x_367_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_367_, 0, v_a_351_);
v___x_368_ = lean_unbox(v_a_334_);
lean_dec(v_a_334_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_368_);
v___x_369_ = lean_unbox(v_a_338_);
lean_dec(v_a_338_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1 + 1, v___x_369_);
v___x_370_ = lean_unbox(v_a_342_);
lean_dec(v_a_342_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1 + 2, v___x_370_);
v___x_371_ = lean_unbox(v_a_346_);
lean_dec(v_a_346_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1 + 3, v___x_371_);
v___x_372_ = lean_unbox(v_a_355_);
lean_dec(v_a_355_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1 + 4, v___x_372_);
v___x_373_ = lean_unbox(v_a_359_);
lean_dec(v_a_359_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1 + 5, v___x_373_);
v___x_374_ = lean_unbox(v_a_363_);
lean_dec(v_a_363_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1 + 6, v___x_374_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_376_ = v___x_365_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_367_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v_a_359_);
lean_dec(v_a_355_);
lean_dec(v_a_351_);
lean_dec(v_a_346_);
lean_dec(v_a_342_);
lean_dec(v_a_338_);
lean_dec(v_a_334_);
v_a_379_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_362_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_362_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_a_355_);
lean_dec(v_a_351_);
lean_dec(v_a_346_);
lean_dec(v_a_342_);
lean_dec(v_a_338_);
lean_dec(v_a_334_);
v_a_387_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_358_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_358_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_a_351_);
lean_dec(v_a_346_);
lean_dec(v_a_342_);
lean_dec(v_a_338_);
lean_dec(v_a_334_);
v_a_395_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_354_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_354_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_a_346_);
lean_dec(v_a_342_);
lean_dec(v_a_338_);
lean_dec(v_a_334_);
v_a_403_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_350_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_350_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_a_342_);
lean_dec(v_a_338_);
lean_dec(v_a_334_);
lean_dec_ref(v___x_322_);
v_a_411_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_345_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_345_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_a_338_);
lean_dec(v_a_334_);
lean_dec_ref(v___x_322_);
v_a_419_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_341_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_341_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_a_334_);
lean_dec_ref(v___x_322_);
v_a_427_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_337_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_337_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
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
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec_ref(v___x_322_);
v_a_435_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_333_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_333_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v___x_459_, lean_object* v___x_460_, lean_object* v_ctor_461_, lean_object* v_args_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(v___x_459_, v___x_460_, v_ctor_461_, v_args_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_args_462_);
lean_dec_ref(v_ctor_461_);
lean_dec_ref(v___x_459_);
return v_res_468_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_470_ = l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___f_473_; 
v___x_471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0);
v___x_472_ = l_Lean_instInhabitedExpr;
v___f_473_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___boxed), 9, 2);
lean_closure_set(v___f_473_, 0, v___x_472_);
lean_closure_set(v___f_473_, 1, v___x_471_);
return v___f_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___f_488_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1);
v___x_489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_490_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_489_, v___f_488_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_498_, lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_506_, lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_506_, v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_box(0);
v___x_516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_517_ = l_Lean_Expr_const___override(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2);
v___x_521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__0));
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(lean_object* v_e_524_, lean_object* v___y_525_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = l_Lean_Expr_hasMVar(v_e_524_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_e_524_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v_mctx_530_; lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; lean_object* v___x_534_; lean_object* v_cache_535_; lean_object* v_zetaDeltaFVarIds_536_; lean_object* v_postponed_537_; lean_object* v_diag_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_547_; 
v___x_529_ = lean_st_ref_get(v___y_525_);
v_mctx_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_mctx_530_);
lean_dec(v___x_529_);
v___x_531_ = l_Lean_instantiateMVarsCore(v_mctx_530_, v_e_524_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_fst_532_);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_531_);
v___x_534_ = lean_st_ref_take(v___y_525_);
v_cache_535_ = lean_ctor_get(v___x_534_, 1);
v_zetaDeltaFVarIds_536_ = lean_ctor_get(v___x_534_, 2);
v_postponed_537_ = lean_ctor_get(v___x_534_, 3);
v_diag_538_ = lean_ctor_get(v___x_534_, 4);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_548_);
v___x_540_ = v___x_534_;
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_diag_538_);
lean_inc(v_postponed_537_);
lean_inc(v_zetaDeltaFVarIds_536_);
lean_inc(v_cache_535_);
lean_dec(v___x_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v_snd_533_);
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_snd_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_cache_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_zetaDeltaFVarIds_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_postponed_537_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_diag_538_);
v___x_543_ = v_reuseFailAlloc_546_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_st_ref_put(v___y_525_, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v_fst_532_);
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg___boxed(lean_object* v_e_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_e_549_, v___y_550_);
lean_dec(v___y_550_);
return v_res_552_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_box(0);
v___x_554_ = l_Lean_Elab_abortTermExceptionId;
v___x_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg(){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___boxed(lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
return v_res_560_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_box(1);
v___x_562_ = l_Lean_MessageData_ofFormat(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__2));
v___x_567_ = l_Lean_MessageData_ofFormat(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
return v_x_568_;
}
else
{
lean_object* v_head_570_; lean_object* v_tail_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_593_; 
v_head_570_ = lean_ctor_get(v_x_569_, 0);
v_tail_571_ = lean_ctor_get(v_x_569_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_569_);
if (v_isSharedCheck_593_ == 0)
{
v___x_573_ = v_x_569_;
v_isShared_574_ = v_isSharedCheck_593_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_tail_571_);
lean_inc(v_head_570_);
lean_dec(v_x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_593_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_before_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_591_; 
v_before_575_ = lean_ctor_get(v_head_570_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_head_570_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_head_570_, 1);
lean_dec(v_unused_592_);
v___x_577_ = v_head_570_;
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_before_575_);
lean_dec(v_head_570_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 7);
lean_ctor_set(v___x_577_, 1, v___x_579_);
lean_ctor_set(v___x_577_, 0, v_x_568_);
v___x_581_ = v___x_577_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_x_568_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_579_);
v___x_581_ = v_reuseFailAlloc_590_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 7);
lean_ctor_set(v___x_573_, 1, v___x_582_);
lean_ctor_set(v___x_573_, 0, v___x_581_);
v___x_584_ = v___x_573_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_589_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = l_Lean_MessageData_ofSyntax(v_before_575_);
v___x_586_ = l_Lean_indentD(v___x_585_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_584_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v_x_568_ = v___x_587_;
v_x_569_ = v_tail_571_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(lean_object* v_opts_594_, lean_object* v_opt_595_){
_start:
{
lean_object* v_name_596_; lean_object* v_defValue_597_; lean_object* v_map_598_; lean_object* v___x_599_; 
v_name_596_ = lean_ctor_get(v_opt_595_, 0);
v_defValue_597_ = lean_ctor_get(v_opt_595_, 1);
v_map_598_ = lean_ctor_get(v_opts_594_, 0);
v___x_599_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_598_, v_name_596_);
if (lean_obj_tag(v___x_599_) == 0)
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_defValue_597_);
return v___x_600_;
}
else
{
lean_object* v_val_601_; 
v_val_601_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v___x_599_, 1);
if (lean_obj_tag(v_val_601_) == 1)
{
uint8_t v_v_602_; 
v_v_602_ = lean_ctor_get_uint8(v_val_601_, 0);
lean_dec_ref_known(v_val_601_, 0);
return v_v_602_;
}
else
{
uint8_t v___x_603_; 
lean_dec(v_val_601_);
v___x_603_ = lean_unbox(v_defValue_597_);
return v___x_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6___boxed(lean_object* v_opts_604_, lean_object* v_opt_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(v_opts_604_, v_opt_605_);
lean_dec_ref(v_opt_605_);
lean_dec_ref(v_opts_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__1));
v___x_612_ = l_Lean_MessageData_ofFormat(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(lean_object* v_msgData_613_, lean_object* v_macroStack_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_615_);
v___x_618_ = l_Lean_Elab_pp_macroStack;
v___x_619_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(v___x_617_, v___x_618_);
lean_dec_ref(v___x_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v_macroStack_614_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_msgData_613_);
return v___x_620_;
}
else
{
if (lean_obj_tag(v_macroStack_614_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_msgData_613_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_after_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_638_; 
v_head_622_ = lean_ctor_get(v_macroStack_614_, 0);
lean_inc(v_head_622_);
v_after_623_ = lean_ctor_get(v_head_622_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_head_622_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v_head_622_, 0);
lean_dec(v_unused_639_);
v___x_625_ = v_head_622_;
v_isShared_626_ = v_isSharedCheck_638_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_after_623_);
lean_dec(v_head_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_638_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 7);
lean_ctor_set(v___x_625_, 1, v___x_627_);
lean_ctor_set(v___x_625_, 0, v_msgData_613_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_msgData_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_637_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_msgData_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_630_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_MessageData_ofSyntax(v_after_623_);
v___x_633_ = l_Lean_indentD(v___x_632_);
v_msgData_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_634_, 0, v___x_631_);
lean_ctor_set(v_msgData_634_, 1, v___x_633_);
v___x_635_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7(v_msgData_634_, v_macroStack_614_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_640_, lean_object* v_macroStack_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_msgData_640_, v_macroStack_641_, v___y_642_);
lean_dec_ref(v___y_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_ref_653_; lean_object* v_macroStack_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_a_657_; lean_object* v___x_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
v_ref_653_ = lean_ctor_get(v___y_650_, 2);
v_macroStack_654_ = lean_ctor_get(v___y_646_, 1);
v___x_655_ = l_Lean_Elab_getBetterRef(v_ref_653_, v_macroStack_654_);
v___x_656_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_645_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref(v___x_656_);
lean_inc(v_macroStack_654_);
v___x_658_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_a_657_, v_macroStack_654_, v___y_650_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_655_);
lean_ctor_set(v___x_663_, 1, v_a_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
lean_ctor_set(v___x_661_, 0, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg___boxed(lean_object* v_msg_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v_msg_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_676_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__0));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__2));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__4));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__6));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__8));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_700_; lean_object* v_evalExpr_701_; lean_object* v_expectedType_x3f_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_toCold_708_; lean_object* v_currRecDepth_709_; lean_object* v_ref_710_; uint16_t v_optionFlags_711_; uint8_t v_suppressElabErrors_712_; uint8_t v_isRecordingDeps_713_; uint8_t v___x_714_; lean_object* v_ref_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_700_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0);
v_evalExpr_701_ = lean_ctor_get(v___x_700_, 0);
v_expectedType_x3f_702_ = lean_ctor_get(v___x_700_, 1);
v___x_703_ = 1;
v___x_704_ = lean_box(0);
v___x_705_ = lean_box(v___x_703_);
v___x_706_ = lean_box(v___x_703_);
lean_inc(v_expectedType_x3f_702_);
lean_inc(v_stx_692_);
v___x_707_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_707_, 0, v_stx_692_);
lean_closure_set(v___x_707_, 1, v_expectedType_x3f_702_);
lean_closure_set(v___x_707_, 2, v___x_705_);
lean_closure_set(v___x_707_, 3, v___x_706_);
lean_closure_set(v___x_707_, 4, v___x_704_);
v_toCold_708_ = lean_ctor_get(v_a_697_, 0);
v_currRecDepth_709_ = lean_ctor_get(v_a_697_, 1);
v_ref_710_ = lean_ctor_get(v_a_697_, 2);
v_optionFlags_711_ = lean_ctor_get_uint16(v_a_697_, sizeof(void*)*3);
v_suppressElabErrors_712_ = lean_ctor_get_uint8(v_a_697_, sizeof(void*)*3 + 2);
v_isRecordingDeps_713_ = lean_ctor_get_uint8(v_a_697_, sizeof(void*)*3 + 3);
v___x_714_ = 1;
v_ref_715_ = l_Lean_replaceRef(v_stx_692_, v_ref_710_);
lean_dec(v_stx_692_);
lean_inc(v_currRecDepth_709_);
lean_inc_ref(v_toCold_708_);
v___x_716_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_716_, 0, v_toCold_708_);
lean_ctor_set(v___x_716_, 1, v_currRecDepth_709_);
lean_ctor_set(v___x_716_, 2, v_ref_715_);
lean_ctor_set_uint16(v___x_716_, sizeof(void*)*3, v_optionFlags_711_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*3 + 2, v_suppressElabErrors_712_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*3 + 3, v_isRecordingDeps_713_);
v___x_717_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_707_, v___x_714_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v___x_716_, v_a_698_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; uint8_t v___x_818_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_a_718_, v_a_696_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
v___x_818_ = l_Lean_Expr_hasSorry(v_a_720_);
if (v___x_818_ == 0)
{
v___y_763_ = v_a_693_;
v___y_764_ = v_a_694_;
v___y_765_ = v_a_695_;
v___y_766_ = v_a_696_;
v___y_767_ = v___x_716_;
v___y_768_ = v_a_698_;
goto v___jp_762_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Expr_hasSyntheticSorry(v_a_720_);
if (v___x_819_ == 0)
{
v___y_800_ = v_a_693_;
v___y_801_ = v_a_694_;
v___y_802_ = v_a_695_;
v___y_803_ = v_a_696_;
v___y_804_ = v___x_716_;
v___y_805_ = v_a_698_;
goto v___jp_799_;
}
else
{
lean_object* v___x_820_; lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_a_720_);
lean_dec_ref_known(v___x_716_, 3);
v___x_820_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
v___jp_721_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_729_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1);
v___x_730_ = l_Lean_indentExpr(v_a_720_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___y_728_);
v___x_733_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_732_, v___y_726_, v___y_725_, v___y_722_, v___y_727_, v___y_724_, v___y_723_);
lean_dec_ref(v___y_724_);
return v___x_733_;
}
v___jp_734_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc_ref(v_evalExpr_701_);
lean_inc(v___y_740_);
lean_inc_ref(v___y_739_);
lean_inc(v___y_738_);
lean_inc_ref(v___y_737_);
lean_inc(v_a_720_);
v___x_742_ = lean_apply_6(v_evalExpr_701_, v_a_720_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, lean_box(0));
if (lean_obj_tag(v___x_742_) == 0)
{
lean_dec_ref(v___y_739_);
lean_dec(v_a_720_);
return v___x_742_;
}
else
{
lean_object* v_a_743_; uint8_t v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
v___x_744_ = l_Lean_Exception_isInterrupt(v_a_743_);
if (v___x_744_ == 0)
{
uint8_t v___x_745_; 
lean_inc(v_a_743_);
v___x_745_ = l_Lean_Exception_isRuntime(v_a_743_);
if (v___x_745_ == 0)
{
if (lean_obj_tag(v_a_743_) == 0)
{
lean_dec_ref_known(v_a_743_, 2);
lean_dec_ref(v___y_739_);
lean_dec(v_a_720_);
return v___x_742_;
}
else
{
lean_object* v_id_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_760_; 
v_id_746_ = lean_ctor_get(v_a_743_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_a_743_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v_a_743_, 1);
lean_dec(v_unused_761_);
v___x_748_ = v_a_743_;
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_id_746_);
lean_dec(v_a_743_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v___x_750_; 
v___x_750_ = l_Lean_instBEqInternalExceptionId_beq(v___x_741_, v_id_746_);
lean_dec(v_id_746_);
if (v___x_750_ == 0)
{
lean_del_object(v___x_748_);
lean_dec_ref(v___y_739_);
lean_dec(v_a_720_);
return v___x_742_;
}
else
{
lean_dec_ref_known(v___x_742_, 1);
if (lean_obj_tag(v_expectedType_x3f_702_) == 1)
{
lean_object* v_val_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v_val_751_ = lean_ctor_get(v_expectedType_x3f_702_, 0);
v___x_752_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3);
lean_inc(v_val_751_);
v___x_753_ = l_Lean_MessageData_ofExpr(v_val_751_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 7);
lean_ctor_set(v___x_748_, 1, v___x_753_);
lean_ctor_set(v___x_748_, 0, v___x_752_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_758_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___y_722_ = v___y_737_;
v___y_723_ = v___y_740_;
v___y_724_ = v___y_739_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_735_;
v___y_727_ = v___y_738_;
v___y_728_ = v___x_757_;
goto v___jp_721_;
}
}
else
{
lean_object* v___x_759_; 
lean_del_object(v___x_748_);
v___x_759_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7);
v___y_722_ = v___y_737_;
v___y_723_ = v___y_740_;
v___y_724_ = v___y_739_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_735_;
v___y_727_ = v___y_738_;
v___y_728_ = v___x_759_;
goto v___jp_721_;
}
}
}
}
}
else
{
lean_dec(v_a_743_);
lean_dec_ref(v___y_739_);
lean_dec(v_a_720_);
return v___x_742_;
}
}
else
{
lean_dec(v_a_743_);
lean_dec_ref(v___y_739_);
lean_dec(v_a_720_);
return v___x_742_;
}
}
}
v___jp_762_:
{
lean_object* v___x_769_; 
lean_inc(v_a_720_);
v___x_769_ = l_Lean_Meta_getMVars(v_a_720_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_770_, v___x_704_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v_a_770_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; uint8_t v___x_773_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = lean_unbox(v_a_772_);
lean_dec(v_a_772_);
if (v___x_773_ == 0)
{
v___y_735_ = v___y_763_;
v___y_736_ = v___y_764_;
v___y_737_ = v___y_765_;
v___y_738_ = v___y_766_;
v___y_739_ = v___y_767_;
v___y_740_ = v___y_768_;
goto v___jp_734_;
}
else
{
lean_object* v___x_774_; lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec_ref(v___y_767_);
lean_dec(v_a_720_);
v___x_774_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v___y_767_);
lean_dec(v_a_720_);
v_a_783_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_771_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_771_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v___y_767_);
lean_dec(v_a_720_);
v_a_791_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_769_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_769_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
v___jp_799_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v___x_806_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9);
v___x_807_ = l_Lean_indentExpr(v_a_720_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_808_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec_ref(v___y_804_);
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref_known(v___x_716_, 3);
v_a_829_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_717_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_717_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(v_stx_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
return v_res_845_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
v___x_850_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__1));
v___x_851_ = l_Lean_mkConst(v___x_850_, v___x_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(lean_object* v_stx_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_toCold_861_; lean_object* v_currRecDepth_862_; lean_object* v_ref_863_; uint16_t v_optionFlags_864_; uint8_t v_suppressElabErrors_865_; uint8_t v_isRecordingDeps_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_ref_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_toCold_861_ = lean_ctor_get(v_a_858_, 0);
v_currRecDepth_862_ = lean_ctor_get(v_a_858_, 1);
v_ref_863_ = lean_ctor_get(v_a_858_, 2);
v_optionFlags_864_ = lean_ctor_get_uint16(v_a_858_, sizeof(void*)*3);
v_suppressElabErrors_865_ = lean_ctor_get_uint8(v_a_858_, sizeof(void*)*3 + 2);
v_isRecordingDeps_866_ = lean_ctor_get_uint8(v_a_858_, sizeof(void*)*3 + 3);
v___x_867_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_868_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2);
v___x_869_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__3));
v_ref_870_ = l_Lean_replaceRef(v_stx_853_, v_ref_863_);
lean_inc(v_currRecDepth_862_);
lean_inc_ref(v_toCold_861_);
v___x_871_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_871_, 0, v_toCold_861_);
lean_ctor_set(v___x_871_, 1, v_currRecDepth_862_);
lean_ctor_set(v___x_871_, 2, v_ref_870_);
lean_ctor_set_uint16(v___x_871_, sizeof(void*)*3, v_optionFlags_864_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*3 + 2, v_suppressElabErrors_865_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*3 + 3, v_isRecordingDeps_866_);
lean_inc(v_stx_853_);
v___x_872_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v___x_868_, v___x_869_, v_stx_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v___x_871_, v_a_859_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref_known(v___x_871_, 3);
lean_dec(v_stx_853_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_fst_877_; lean_object* v___x_879_; 
v_fst_877_ = lean_ctor_get(v_a_873_, 0);
lean_inc(v_fst_877_);
lean_dec(v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_fst_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_fst_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_894_; 
v_a_882_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_894_ == 0)
{
v___x_884_ = v___x_872_;
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_872_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
lean_inc(v_a_882_);
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_893_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
uint8_t v___x_888_; 
v___x_888_ = l_Lean_Exception_isInterrupt(v_a_882_);
if (v___x_888_ == 0)
{
uint8_t v___x_889_; 
lean_inc(v_a_882_);
v___x_889_ = l_Lean_Exception_isRuntime(v_a_882_);
if (v___x_889_ == 0)
{
if (lean_obj_tag(v_a_882_) == 0)
{
lean_dec_ref_known(v_a_882_, 2);
lean_dec_ref_known(v___x_871_, 3);
lean_dec(v_stx_853_);
return v___x_887_;
}
else
{
lean_object* v_id_890_; uint8_t v___x_891_; 
v_id_890_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_id_890_);
lean_dec_ref_known(v_a_882_, 2);
v___x_891_ = l_Lean_instBEqInternalExceptionId_beq(v___x_867_, v_id_890_);
lean_dec(v_id_890_);
if (v___x_891_ == 0)
{
lean_dec_ref_known(v___x_871_, 3);
lean_dec(v_stx_853_);
return v___x_887_;
}
else
{
lean_object* v___x_892_; 
lean_dec_ref(v___x_887_);
v___x_892_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(v_stx_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v___x_871_, v_a_859_);
lean_dec_ref_known(v___x_871_, 3);
return v___x_892_;
}
}
}
else
{
lean_dec(v_a_882_);
lean_dec_ref_known(v___x_871_, 3);
lean_dec(v_stx_853_);
return v___x_887_;
}
}
else
{
lean_dec(v_a_882_);
lean_dec_ref_known(v___x_871_, 3);
lean_dec(v_stx_853_);
return v___x_887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(v_stx_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
return v_res_903_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1);
v___x_905_ = l_Lean_MessageData_ofExpr(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0);
v___x_907_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_910_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(lean_object* v_stx_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_ty_x3f_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_toCold_926_; lean_object* v_currRecDepth_927_; lean_object* v_ref_928_; uint16_t v_optionFlags_929_; uint8_t v_suppressElabErrors_930_; uint8_t v_isRecordingDeps_931_; uint8_t v___x_932_; lean_object* v_ref_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_ty_x3f_920_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2);
v___x_921_ = 1;
v___x_922_ = lean_box(0);
v___x_923_ = lean_box(v___x_921_);
v___x_924_ = lean_box(v___x_921_);
lean_inc(v_stx_912_);
v___x_925_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_925_, 0, v_stx_912_);
lean_closure_set(v___x_925_, 1, v_ty_x3f_920_);
lean_closure_set(v___x_925_, 2, v___x_923_);
lean_closure_set(v___x_925_, 3, v___x_924_);
lean_closure_set(v___x_925_, 4, v___x_922_);
v_toCold_926_ = lean_ctor_get(v_a_917_, 0);
v_currRecDepth_927_ = lean_ctor_get(v_a_917_, 1);
v_ref_928_ = lean_ctor_get(v_a_917_, 2);
v_optionFlags_929_ = lean_ctor_get_uint16(v_a_917_, sizeof(void*)*3);
v_suppressElabErrors_930_ = lean_ctor_get_uint8(v_a_917_, sizeof(void*)*3 + 2);
v_isRecordingDeps_931_ = lean_ctor_get_uint8(v_a_917_, sizeof(void*)*3 + 3);
v___x_932_ = 1;
v_ref_933_ = l_Lean_replaceRef(v_stx_912_, v_ref_928_);
lean_dec(v_stx_912_);
lean_inc(v_currRecDepth_927_);
lean_inc_ref(v_toCold_926_);
v___x_934_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_934_, 0, v_toCold_926_);
lean_ctor_set(v___x_934_, 1, v_currRecDepth_927_);
lean_ctor_set(v___x_934_, 2, v_ref_933_);
lean_ctor_set_uint16(v___x_934_, sizeof(void*)*3, v_optionFlags_929_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*3 + 2, v_suppressElabErrors_930_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*3 + 3, v_isRecordingDeps_931_);
v___x_935_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_925_, v___x_932_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v___x_934_, v_a_918_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v_a_938_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; uint8_t v___x_1022_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_a_936_, v_a_916_);
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref(v___x_937_);
v___x_1022_ = l_Lean_Expr_hasSorry(v_a_938_);
if (v___x_1022_ == 0)
{
v___y_967_ = v_a_913_;
v___y_968_ = v_a_914_;
v___y_969_ = v_a_915_;
v___y_970_ = v_a_916_;
v___y_971_ = v___x_934_;
v___y_972_ = v_a_918_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1023_; 
v___x_1023_ = l_Lean_Expr_hasSyntheticSorry(v_a_938_);
if (v___x_1023_ == 0)
{
v___y_1004_ = v_a_913_;
v___y_1005_ = v_a_914_;
v___y_1006_ = v_a_915_;
v___y_1007_ = v_a_916_;
v___y_1008_ = v___x_934_;
v___y_1009_ = v_a_918_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_a_938_);
lean_dec_ref_known(v___x_934_, 3);
v___x_1024_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
v___jp_939_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_938_);
v___x_947_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(v_a_938_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_dec_ref(v___y_944_);
lean_dec(v_a_938_);
return v___x_947_;
}
else
{
lean_object* v_a_948_; uint8_t v___x_949_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
v___x_949_ = l_Lean_Exception_isInterrupt(v_a_948_);
if (v___x_949_ == 0)
{
uint8_t v___x_950_; 
lean_inc(v_a_948_);
v___x_950_ = l_Lean_Exception_isRuntime(v_a_948_);
if (v___x_950_ == 0)
{
if (lean_obj_tag(v_a_948_) == 0)
{
lean_dec_ref_known(v_a_948_, 2);
lean_dec_ref(v___y_944_);
lean_dec(v_a_938_);
return v___x_947_;
}
else
{
lean_object* v_id_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_964_; 
v_id_951_ = lean_ctor_get(v_a_948_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_a_948_, 1);
lean_dec(v_unused_965_);
v___x_953_ = v_a_948_;
v_isShared_954_ = v_isSharedCheck_964_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_id_951_);
lean_dec(v_a_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_964_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_instBEqInternalExceptionId_beq(v___x_946_, v_id_951_);
lean_dec(v_id_951_);
if (v___x_955_ == 0)
{
lean_del_object(v___x_953_);
lean_dec_ref(v___y_944_);
lean_dec(v_a_938_);
return v___x_947_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec_ref_known(v___x_947_, 1);
v___x_956_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2);
v___x_957_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1);
v___x_958_ = l_Lean_indentExpr(v_a_938_);
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 7);
lean_ctor_set(v___x_953_, 1, v___x_958_);
lean_ctor_set(v___x_953_, 0, v___x_957_);
v___x_960_ = v___x_953_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_963_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_956_);
v___x_962_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_961_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec_ref(v___y_944_);
return v___x_962_;
}
}
}
}
}
else
{
lean_dec(v_a_948_);
lean_dec_ref(v___y_944_);
lean_dec(v_a_938_);
return v___x_947_;
}
}
else
{
lean_dec(v_a_948_);
lean_dec_ref(v___y_944_);
lean_dec(v_a_938_);
return v___x_947_;
}
}
}
v___jp_966_:
{
lean_object* v___x_973_; 
lean_inc(v_a_938_);
v___x_973_ = l_Lean_Meta_getMVars(v_a_938_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_974_, v___x_922_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v_a_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; uint8_t v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = lean_unbox(v_a_976_);
lean_dec(v_a_976_);
if (v___x_977_ == 0)
{
v___y_940_ = v___y_967_;
v___y_941_ = v___y_968_;
v___y_942_ = v___y_969_;
v___y_943_ = v___y_970_;
v___y_944_ = v___y_971_;
v___y_945_ = v___y_972_;
goto v___jp_939_;
}
else
{
lean_object* v___x_978_; lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v___y_971_);
lean_dec(v_a_938_);
v___x_978_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v___y_971_);
lean_dec(v_a_938_);
v_a_987_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_975_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_975_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec_ref(v___y_971_);
lean_dec(v_a_938_);
v_a_995_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_973_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_973_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
v___jp_1003_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v___x_1010_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9);
v___x_1011_ = l_Lean_indentExpr(v_a_938_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_1012_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec_ref(v___y_1008_);
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref_known(v___x_934_, 3);
v_a_1033_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_935_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_935_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(v_stx_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(lean_object* v_config_1125_, lean_object* v_item_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_item_1135_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_1139_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1126_, v___x_1138_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1139_) == 0)
{
uint8_t v___x_1140_; 
lean_dec_ref_known(v___x_1139_, 1);
v___x_1140_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1126_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1141_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1126_);
lean_inc_ref(v_item_1126_);
v___x_1142_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1126_);
v___x_1143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__1));
v___x_1144_ = lean_string_dec_lt(v___x_1141_, v___x_1143_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_string_dec_eq(v___x_1141_, v___x_1143_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__2));
v___x_1147_ = lean_string_dec_eq(v___x_1141_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__3));
v___x_1149_ = lean_string_dec_eq(v___x_1141_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__4));
v___x_1151_ = lean_string_dec_eq(v___x_1141_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__5));
v___x_1153_ = lean_string_dec_eq(v___x_1141_, v___x_1152_);
lean_dec_ref(v___x_1141_);
if (v___x_1153_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6));
v___x_1155_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1154_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1155_) == 0)
{
uint8_t v___x_1156_; 
lean_dec_ref_known(v___x_1155_, 1);
v___x_1156_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1156_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1157_; 
lean_dec_ref(v___x_1142_);
v___x_1157_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1180_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1180_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1180_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
uint8_t v_leave_1162_; uint8_t v_elimLets_1163_; uint8_t v_jp_1164_; lean_object* v_stepLimit_1165_; uint8_t v_errorOnMissingSpec_1166_; uint8_t v_debug_1167_; uint8_t v_internalize_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1179_; 
v_leave_1162_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 1);
v_elimLets_1163_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 2);
v_jp_1164_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 3);
v_stepLimit_1165_ = lean_ctor_get(v_config_1125_, 0);
v_errorOnMissingSpec_1166_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 4);
v_debug_1167_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 5);
v_internalize_1168_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 6);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1170_ = v_config_1125_;
v_isShared_1171_ = v_isSharedCheck_1179_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_stepLimit_1165_);
lean_dec(v_config_1125_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1179_;
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
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_stepLimit_1165_);
v___x_1173_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
uint8_t v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_unbox(v_a_1158_);
lean_dec(v_a_1158_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1, v___x_1174_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1 + 1, v_leave_1162_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1 + 2, v_elimLets_1163_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1 + 3, v_jp_1164_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1166_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1 + 5, v_debug_1167_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1 + 6, v_internalize_1168_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1173_);
v___x_1176_ = v___x_1160_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1173_);
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
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_config_1125_);
v_a_1181_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1157_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1157_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1189_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1155_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1155_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec_ref(v___x_1141_);
v___x_1197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7));
v___x_1198_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1197_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1198_) == 0)
{
uint8_t v___x_1199_; 
lean_dec_ref_known(v___x_1198_, 1);
v___x_1199_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1199_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1200_; 
lean_dec_ref(v___x_1142_);
lean_inc_ref(v_item_1126_);
v___x_1200_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_value_1201_; lean_object* v___x_1202_; 
lean_dec_ref_known(v___x_1200_, 1);
v_value_1201_ = lean_ctor_get(v_item_1126_, 2);
lean_inc(v_value_1201_);
lean_dec_ref(v_item_1126_);
v___x_1202_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(v_value_1201_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
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
uint8_t v_trivial_1207_; uint8_t v_leave_1208_; uint8_t v_elimLets_1209_; uint8_t v_jp_1210_; uint8_t v_errorOnMissingSpec_1211_; uint8_t v_debug_1212_; uint8_t v_internalize_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1223_; 
v_trivial_1207_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1);
v_leave_1208_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 1);
v_elimLets_1209_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 2);
v_jp_1210_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 3);
v_errorOnMissingSpec_1211_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 4);
v_debug_1212_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 5);
v_internalize_1213_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 6);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_config_1125_, 0);
lean_dec(v_unused_1224_);
v___x_1215_ = v_config_1125_;
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v_config_1125_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v_a_1203_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*1, v_trivial_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*1 + 1, v_leave_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*1 + 2, v_elimLets_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*1 + 3, v_jp_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*1 + 5, v_debug_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*1 + 6, v_internalize_1213_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1218_);
v___x_1220_ = v___x_1205_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
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
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_config_1125_);
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
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
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
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1242_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1198_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1198_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref(v___x_1141_);
v___x_1250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8));
v___x_1251_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1250_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1251_) == 0)
{
uint8_t v___x_1252_; 
lean_dec_ref_known(v___x_1251_, 1);
v___x_1252_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1252_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1253_; 
lean_dec_ref(v___x_1142_);
v___x_1253_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1276_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1276_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1276_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v_trivial_1258_; uint8_t v_elimLets_1259_; uint8_t v_jp_1260_; lean_object* v_stepLimit_1261_; uint8_t v_errorOnMissingSpec_1262_; uint8_t v_debug_1263_; uint8_t v_internalize_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1275_; 
v_trivial_1258_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1);
v_elimLets_1259_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 2);
v_jp_1260_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 3);
v_stepLimit_1261_ = lean_ctor_get(v_config_1125_, 0);
v_errorOnMissingSpec_1262_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 4);
v_debug_1263_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 5);
v_internalize_1264_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 6);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1266_ = v_config_1125_;
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_stepLimit_1261_);
lean_dec(v_config_1125_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1275_;
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
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_stepLimit_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*1, v_trivial_1258_);
v___x_1269_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
uint8_t v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_unbox(v_a_1254_);
lean_dec(v_a_1254_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*1 + 1, v___x_1270_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*1 + 2, v_elimLets_1259_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*1 + 3, v_jp_1260_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1262_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*1 + 5, v_debug_1263_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*1 + 6, v_internalize_1264_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1269_);
v___x_1272_ = v___x_1256_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1269_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_config_1125_);
v_a_1277_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1253_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1253_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1285_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1251_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1251_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v___x_1141_);
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9));
v___x_1294_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1293_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1294_) == 0)
{
uint8_t v___x_1295_; 
lean_dec_ref_known(v___x_1294_, 1);
v___x_1295_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1296_; 
lean_dec_ref(v___x_1142_);
v___x_1296_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1319_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1319_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1319_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
uint8_t v_trivial_1301_; uint8_t v_leave_1302_; uint8_t v_elimLets_1303_; lean_object* v_stepLimit_1304_; uint8_t v_errorOnMissingSpec_1305_; uint8_t v_debug_1306_; uint8_t v_internalize_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1318_; 
v_trivial_1301_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1);
v_leave_1302_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 1);
v_elimLets_1303_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 2);
v_stepLimit_1304_ = lean_ctor_get(v_config_1125_, 0);
v_errorOnMissingSpec_1305_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 4);
v_debug_1306_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 5);
v_internalize_1307_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 6);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1309_ = v_config_1125_;
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_stepLimit_1304_);
lean_dec(v_config_1125_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1318_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_stepLimit_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*1, v_trivial_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*1 + 1, v_leave_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, sizeof(void*)*1 + 2, v_elimLets_1303_);
v___x_1312_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
uint8_t v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_unbox(v_a_1297_);
lean_dec(v_a_1297_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*1 + 3, v___x_1313_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1305_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*1 + 5, v_debug_1306_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*1 + 6, v_internalize_1307_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1312_);
v___x_1315_ = v___x_1299_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1312_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_config_1125_);
v_a_1320_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1296_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1296_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1328_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1294_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1294_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v___x_1141_);
v___x_1336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10));
v___x_1337_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1336_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1337_) == 0)
{
uint8_t v___x_1338_; 
lean_dec_ref_known(v___x_1337_, 1);
v___x_1338_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1339_; 
lean_dec_ref(v___x_1142_);
v___x_1339_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1362_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1362_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1362_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint8_t v_trivial_1344_; uint8_t v_leave_1345_; uint8_t v_elimLets_1346_; uint8_t v_jp_1347_; lean_object* v_stepLimit_1348_; uint8_t v_errorOnMissingSpec_1349_; uint8_t v_debug_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1361_; 
v_trivial_1344_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1);
v_leave_1345_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 1);
v_elimLets_1346_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 2);
v_jp_1347_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 3);
v_stepLimit_1348_ = lean_ctor_get(v_config_1125_, 0);
v_errorOnMissingSpec_1349_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 4);
v_debug_1350_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 5);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1352_ = v_config_1125_;
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_stepLimit_1348_);
lean_dec(v_config_1125_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_stepLimit_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*1, v_trivial_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*1 + 1, v_leave_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*1 + 2, v_elimLets_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*1 + 3, v_jp_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*1 + 5, v_debug_1350_);
v___x_1355_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
uint8_t v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_unbox(v_a_1340_);
lean_dec(v_a_1340_);
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*1 + 6, v___x_1356_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1355_);
v___x_1358_ = v___x_1342_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1355_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v_config_1125_);
v_a_1363_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1339_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1339_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1371_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1337_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1337_);
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
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__11));
v___x_1380_ = lean_string_dec_eq(v___x_1141_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__12));
v___x_1382_ = lean_string_dec_eq(v___x_1141_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__13));
v___x_1384_ = lean_string_dec_eq(v___x_1141_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__14));
v___x_1386_ = lean_string_dec_eq(v___x_1141_, v___x_1385_);
lean_dec_ref(v___x_1141_);
if (v___x_1386_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15));
v___x_1388_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1387_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1388_) == 0)
{
uint8_t v___x_1389_; 
lean_dec_ref_known(v___x_1388_, 1);
v___x_1389_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1389_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1390_; 
lean_dec_ref(v___x_1142_);
v___x_1390_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1413_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1413_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1413_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v_trivial_1395_; uint8_t v_leave_1396_; uint8_t v_elimLets_1397_; uint8_t v_jp_1398_; lean_object* v_stepLimit_1399_; uint8_t v_debug_1400_; uint8_t v_internalize_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1412_; 
v_trivial_1395_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1);
v_leave_1396_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 1);
v_elimLets_1397_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 2);
v_jp_1398_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 3);
v_stepLimit_1399_ = lean_ctor_get(v_config_1125_, 0);
v_debug_1400_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 5);
v_internalize_1401_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 6);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1403_ = v_config_1125_;
v_isShared_1404_ = v_isSharedCheck_1412_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_stepLimit_1399_);
lean_dec(v_config_1125_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1412_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_stepLimit_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*1, v_trivial_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*1 + 1, v_leave_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*1 + 2, v_elimLets_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*1 + 3, v_jp_1398_);
v___x_1406_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
uint8_t v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_unbox(v_a_1391_);
lean_dec(v_a_1391_);
lean_ctor_set_uint8(v___x_1406_, sizeof(void*)*1 + 4, v___x_1407_);
lean_ctor_set_uint8(v___x_1406_, sizeof(void*)*1 + 5, v_debug_1400_);
lean_ctor_set_uint8(v___x_1406_, sizeof(void*)*1 + 6, v_internalize_1401_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1406_);
v___x_1409_ = v___x_1393_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
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
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_config_1125_);
v_a_1414_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1390_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1390_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1422_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1388_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1388_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v___x_1141_);
v___x_1430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16));
v___x_1431_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1430_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1431_) == 0)
{
uint8_t v___x_1432_; 
lean_dec_ref_known(v___x_1431_, 1);
v___x_1432_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1432_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1433_; 
lean_dec_ref(v___x_1142_);
v___x_1433_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1456_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1456_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1456_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v_trivial_1438_; uint8_t v_leave_1439_; uint8_t v_jp_1440_; lean_object* v_stepLimit_1441_; uint8_t v_errorOnMissingSpec_1442_; uint8_t v_debug_1443_; uint8_t v_internalize_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1455_; 
v_trivial_1438_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1);
v_leave_1439_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 1);
v_jp_1440_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 3);
v_stepLimit_1441_ = lean_ctor_get(v_config_1125_, 0);
v_errorOnMissingSpec_1442_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 4);
v_debug_1443_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 5);
v_internalize_1444_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 6);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1446_ = v_config_1125_;
v_isShared_1447_ = v_isSharedCheck_1455_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_stepLimit_1441_);
lean_dec(v_config_1125_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1455_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_stepLimit_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*1, v_trivial_1438_);
lean_ctor_set_uint8(v_reuseFailAlloc_1454_, sizeof(void*)*1 + 1, v_leave_1439_);
v___x_1449_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
uint8_t v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_unbox(v_a_1434_);
lean_dec(v_a_1434_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1 + 2, v___x_1450_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1 + 3, v_jp_1440_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1442_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1 + 5, v_debug_1443_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1 + 6, v_internalize_1444_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1449_);
v___x_1452_ = v___x_1436_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1449_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_config_1125_);
v_a_1457_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1433_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1433_);
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
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1465_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1431_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1431_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v___x_1141_);
v___x_1473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17));
v___x_1474_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1126_, v___x_1473_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1474_) == 0)
{
uint8_t v___x_1475_; 
lean_dec_ref_known(v___x_1474_, 1);
v___x_1475_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1475_ == 0)
{
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v___x_1476_; 
lean_dec_ref(v___x_1142_);
v___x_1476_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1499_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1499_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1499_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
uint8_t v_trivial_1481_; uint8_t v_leave_1482_; uint8_t v_elimLets_1483_; uint8_t v_jp_1484_; lean_object* v_stepLimit_1485_; uint8_t v_errorOnMissingSpec_1486_; uint8_t v_internalize_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1498_; 
v_trivial_1481_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1);
v_leave_1482_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 1);
v_elimLets_1483_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 2);
v_jp_1484_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 3);
v_stepLimit_1485_ = lean_ctor_get(v_config_1125_, 0);
v_errorOnMissingSpec_1486_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 4);
v_internalize_1487_ = lean_ctor_get_uint8(v_config_1125_, sizeof(void*)*1 + 6);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_config_1125_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1489_ = v_config_1125_;
v_isShared_1490_ = v_isSharedCheck_1498_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_stepLimit_1485_);
lean_dec(v_config_1125_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1498_;
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
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_stepLimit_1485_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*1, v_trivial_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*1 + 1, v_leave_1482_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*1 + 2, v_elimLets_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*1 + 3, v_jp_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1486_);
v___x_1492_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
uint8_t v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_unbox(v_a_1477_);
lean_dec(v_a_1477_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*1 + 5, v___x_1493_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*1 + 6, v_internalize_1487_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1492_);
v___x_1495_ = v___x_1479_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1492_);
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
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v_config_1125_);
v_a_1500_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1476_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1476_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1508_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1474_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1474_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
else
{
uint8_t v___x_1516_; 
lean_dec_ref(v___x_1141_);
lean_dec_ref(v_config_1125_);
v___x_1516_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1142_);
if (v___x_1516_ == 0)
{
lean_dec_ref(v_item_1126_);
v_item_1135_ = v___x_1142_;
goto v___jp_1134_;
}
else
{
lean_object* v_value_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v___x_1142_);
v_value_1517_ = lean_ctor_get(v_item_1126_, 2);
lean_inc(v_value_1517_);
lean_dec_ref(v_item_1126_);
v___x_1518_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(v_value_1517_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1518_;
}
}
}
}
else
{
lean_dec_ref(v_config_1125_);
v_item_1135_ = v_item_1126_;
goto v___jp_1134_;
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_item_1126_);
lean_dec_ref(v_config_1125_);
v_a_1519_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1139_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1139_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
v___jp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__0));
v___x_1137_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1135_, v___x_1136_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1527_, lean_object* v_item_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(v_config_1527_, v_item_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(lean_object* v_e_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_e_1539_, v___y_1543_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_e_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(v_e_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4(lean_object* v_00_u03b1_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4(v_00_u03b1_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(lean_object* v_00_u03b1_1575_, lean_object* v_msg_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v_msg_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_msg_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(v_00_u03b1_1585_, v_msg_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(lean_object* v_msgData_1595_, lean_object* v_macroStack_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_msgData_1595_, v_macroStack_1596_, v___y_1601_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___boxed(lean_object* v_msgData_1605_, lean_object* v_macroStack_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(v_msgData_1605_, v_macroStack_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1614_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_box(0);
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_1617_ = l_Lean_mkConst(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(lean_object* v_cfg_1620_, lean_object* v_cfgItem_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1);
v___x_1630_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_1620_, v_cfgItem_1621_, v___x_1629_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___boxed(lean_object* v_cfg_1631_, lean_object* v_cfgItem_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(v_cfg_1631_, v_cfgItem_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v_cfgItem_1632_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg(lean_object* v_cfg_1642_, lean_object* v_init_1643_, uint8_t v_logExceptions_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_onErr_1649_; lean_object* v_eval_1650_; 
v_onErr_1649_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0));
v_eval_1650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___closed__0));
if (v_logExceptions_1644_ == 0)
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1650_, v_init_1643_, v_cfg_1642_, v_onErr_1649_, v_logExceptions_1644_, v_a_1646_, v_a_1647_);
return v___x_1651_;
}
else
{
uint8_t v_recover_1652_; lean_object* v___x_1653_; 
v_recover_1652_ = lean_ctor_get_uint8(v_a_1645_, sizeof(void*)*1);
v___x_1653_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1650_, v_init_1643_, v_cfg_1642_, v_onErr_1649_, v_recover_1652_, v_a_1646_, v_a_1647_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___boxed(lean_object* v_cfg_1654_, lean_object* v_init_1655_, lean_object* v_logExceptions_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
uint8_t v_logExceptions_boxed_1661_; lean_object* v_res_1662_; 
v_logExceptions_boxed_1661_ = lean_unbox(v_logExceptions_1656_);
v_res_1662_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_cfg_1654_, v_init_1655_, v_logExceptions_boxed_1661_, v_a_1657_, v_a_1658_, v_a_1659_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig(lean_object* v_cfg_1663_, lean_object* v_init_1664_, uint8_t v_logExceptions_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_cfg_1663_, v_init_1664_, v_logExceptions_1665_, v_a_1666_, v_a_1672_, v_a_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object* v_cfg_1676_, lean_object* v_init_1677_, lean_object* v_logExceptions_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
uint8_t v_logExceptions_boxed_1688_; lean_object* v_res_1689_; 
v_logExceptions_boxed_1688_ = lean_unbox(v_logExceptions_1678_);
v_res_1689_ = l_Lean_Elab_Tactic_Do_elabConfig(v_cfg_1676_, v_init_1677_, v_logExceptions_boxed_1688_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg(lean_object* v_a_1690_){
_start:
{
lean_object* v___x_1695_; lean_object* v_fuel_1696_; 
v___x_1695_ = lean_st_ref_get(v_a_1690_);
v_fuel_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_fuel_1696_);
if (lean_obj_tag(v_fuel_1696_) == 0)
{
lean_object* v_simpState_1697_; lean_object* v_invariants_1698_; lean_object* v_vcs_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1721_; 
v_simpState_1697_ = lean_ctor_get(v___x_1695_, 1);
v_invariants_1698_ = lean_ctor_get(v___x_1695_, 2);
v_vcs_1699_ = lean_ctor_get(v___x_1695_, 3);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v___x_1695_, 0);
lean_dec(v_unused_1722_);
v___x_1701_ = v___x_1695_;
v_isShared_1702_ = v_isSharedCheck_1721_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_vcs_1699_);
lean_inc(v_invariants_1698_);
lean_inc(v_simpState_1697_);
lean_dec(v___x_1695_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1721_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_n_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1720_; 
v_n_1703_ = lean_ctor_get(v_fuel_1696_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_fuel_1696_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1705_ = v_fuel_1696_;
v_isShared_1706_ = v_isSharedCheck_1720_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_n_1703_);
lean_dec(v_fuel_1696_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1720_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_zero_1707_; uint8_t v_isZero_1708_; 
v_zero_1707_ = lean_unsigned_to_nat(0u);
v_isZero_1708_ = lean_nat_dec_eq(v_n_1703_, v_zero_1707_);
if (v_isZero_1708_ == 1)
{
lean_del_object(v___x_1705_);
lean_dec(v_n_1703_);
lean_del_object(v___x_1701_);
lean_dec_ref(v_vcs_1699_);
lean_dec_ref(v_invariants_1698_);
lean_dec_ref(v_simpState_1697_);
goto v___jp_1692_;
}
else
{
lean_object* v_one_1709_; lean_object* v_n_1710_; lean_object* v___x_1712_; 
v_one_1709_ = lean_unsigned_to_nat(1u);
v_n_1710_ = lean_nat_sub(v_n_1703_, v_one_1709_);
lean_dec(v_n_1703_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v_n_1710_);
v___x_1712_ = v___x_1705_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_n_1710_);
v___x_1712_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1712_);
v___x_1714_ = v___x_1701_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_simpState_1697_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_invariants_1698_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_vcs_1699_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = lean_st_ref_swap(v_a_1690_, v___x_1714_);
lean_dec(v___x_1716_);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
return v___x_1717_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1695_);
goto v___jp_1692_;
}
v___jp_1692_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg___boxed(lean_object* v_a_1723_, lean_object* v_a_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1723_);
lean_dec(v_a_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne(lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1727_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___boxed(lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Elab_Tactic_Do_burnOne(v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(lean_object* v_x_1742_, lean_object* v_k_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v_fuel_1752_; 
v___x_1751_ = lean_st_ref_get(v_a_1745_);
v_fuel_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_fuel_1752_);
lean_dec(v___x_1751_);
if (lean_obj_tag(v_fuel_1752_) == 0)
{
lean_object* v_n_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_n_1753_ = lean_ctor_get(v_fuel_1752_, 0);
lean_inc(v_n_1753_);
lean_dec_ref_known(v_fuel_1752_, 1);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_nat_dec_eq(v_n_1753_, v___x_1754_);
lean_dec(v_n_1753_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_dec_ref(v_x_1742_);
lean_inc(v_a_1749_);
lean_inc_ref(v_a_1748_);
lean_inc(v_a_1747_);
lean_inc_ref(v_a_1746_);
lean_inc(v_a_1745_);
lean_inc_ref(v_a_1744_);
v___x_1756_ = lean_apply_7(v_k_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, lean_box(0));
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; 
lean_dec_ref(v_k_1743_);
lean_inc(v_a_1749_);
lean_inc_ref(v_a_1748_);
lean_inc(v_a_1747_);
lean_inc_ref(v_a_1746_);
lean_inc(v_a_1745_);
lean_inc_ref(v_a_1744_);
v___x_1757_ = lean_apply_7(v_x_1742_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, lean_box(0));
return v___x_1757_;
}
}
else
{
lean_object* v___x_1758_; 
lean_dec(v_fuel_1752_);
lean_dec_ref(v_x_1742_);
lean_inc(v_a_1749_);
lean_inc_ref(v_a_1748_);
lean_inc(v_a_1747_);
lean_inc_ref(v_a_1746_);
lean_inc(v_a_1745_);
lean_inc_ref(v_a_1744_);
v___x_1758_ = lean_apply_7(v_k_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, lean_box(0));
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg___boxed(lean_object* v_x_1759_, lean_object* v_k_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1759_, v_k_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel(lean_object* v_00_u03b1_1769_, lean_object* v_x_1770_, lean_object* v_k_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1770_, v_k_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___boxed(lean_object* v_00_u03b1_1780_, lean_object* v_x_1781_, lean_object* v_k_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel(v_00_u03b1_1780_, v_x_1781_, v_k_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v_ks_1795_; lean_object* v_vs_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1820_; 
v_ks_1795_ = lean_ctor_get(v_x_1791_, 0);
v_vs_1796_ = lean_ctor_get(v_x_1791_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_x_1791_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1798_ = v_x_1791_;
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_vs_1796_);
lean_inc(v_ks_1795_);
lean_dec(v_x_1791_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_array_get_size(v_ks_1795_);
v___x_1801_ = lean_nat_dec_lt(v_x_1792_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec(v_x_1792_);
v___x_1802_ = lean_array_push(v_ks_1795_, v_x_1793_);
v___x_1803_ = lean_array_push(v_vs_1796_, v_x_1794_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 1, v___x_1803_);
lean_ctor_set(v___x_1798_, 0, v___x_1802_);
v___x_1805_ = v___x_1798_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_object* v_k_x27_1807_; uint8_t v___x_1808_; 
v_k_x27_1807_ = lean_array_fget_borrowed(v_ks_1795_, v_x_1792_);
v___x_1808_ = l_Lean_instBEqMVarId_beq(v_x_1793_, v_k_x27_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1810_; 
if (v_isShared_1799_ == 0)
{
v___x_1810_ = v___x_1798_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_ks_1795_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_vs_1796_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_unsigned_to_nat(1u);
v___x_1812_ = lean_nat_add(v_x_1792_, v___x_1811_);
lean_dec(v_x_1792_);
v_x_1791_ = v___x_1810_;
v_x_1792_ = v___x_1812_;
goto _start;
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1815_ = lean_array_fset(v_ks_1795_, v_x_1792_, v_x_1793_);
v___x_1816_ = lean_array_fset(v_vs_1796_, v_x_1792_, v_x_1794_);
lean_dec(v_x_1792_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 1, v___x_1816_);
lean_ctor_set(v___x_1798_, 0, v___x_1815_);
v___x_1818_ = v___x_1798_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1816_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_n_1821_, lean_object* v_k_1822_, lean_object* v_v_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_n_1821_, v___x_1824_, v_k_1822_, v_v_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1827_, size_t v_x_1828_, size_t v_x_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
lean_object* v_es_1832_; size_t v___x_1833_; size_t v___x_1834_; lean_object* v_j_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_es_1832_ = lean_ctor_get(v_x_1827_, 0);
v___x_1833_ = ((size_t)31ULL);
v___x_1834_ = lean_usize_land(v_x_1828_, v___x_1833_);
v_j_1835_ = lean_usize_to_nat(v___x_1834_);
v___x_1836_ = lean_array_get_size(v_es_1832_);
v___x_1837_ = lean_nat_dec_lt(v_j_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_dec(v_j_1835_);
lean_dec(v_x_1831_);
lean_dec(v_x_1830_);
return v_x_1827_;
}
else
{
lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1876_; 
lean_inc_ref(v_es_1832_);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v_x_1827_, 0);
lean_dec(v_unused_1877_);
v___x_1839_ = v_x_1827_;
v_isShared_1840_ = v_isSharedCheck_1876_;
goto v_resetjp_1838_;
}
else
{
lean_dec(v_x_1827_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1876_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_v_1841_; lean_object* v___x_1842_; lean_object* v_xs_x27_1843_; lean_object* v___y_1845_; 
v_v_1841_ = lean_array_fget(v_es_1832_, v_j_1835_);
v___x_1842_ = lean_box(0);
v_xs_x27_1843_ = lean_array_fset(v_es_1832_, v_j_1835_, v___x_1842_);
switch(lean_obj_tag(v_v_1841_))
{
case 0:
{
lean_object* v_key_1850_; lean_object* v_val_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1861_; 
v_key_1850_ = lean_ctor_get(v_v_1841_, 0);
v_val_1851_ = lean_ctor_get(v_v_1841_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_v_1841_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1853_ = v_v_1841_;
v_isShared_1854_ = v_isSharedCheck_1861_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_val_1851_);
lean_inc(v_key_1850_);
lean_dec(v_v_1841_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1861_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
uint8_t v___x_1855_; 
v___x_1855_ = l_Lean_instBEqMVarId_beq(v_x_1830_, v_key_1850_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_del_object(v___x_1853_);
v___x_1856_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1850_, v_val_1851_, v_x_1830_, v_x_1831_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
v___y_1845_ = v___x_1857_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1859_; 
lean_dec(v_val_1851_);
lean_dec(v_key_1850_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v_x_1831_);
lean_ctor_set(v___x_1853_, 0, v_x_1830_);
v___x_1859_ = v___x_1853_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_x_1830_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_x_1831_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
v___y_1845_ = v___x_1859_;
goto v___jp_1844_;
}
}
}
}
case 1:
{
lean_object* v_node_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1874_; 
v_node_1862_ = lean_ctor_get(v_v_1841_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_v_1841_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1864_ = v_v_1841_;
v_isShared_1865_ = v_isSharedCheck_1874_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_node_1862_);
lean_dec(v_v_1841_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1874_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
size_t v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1866_ = ((size_t)5ULL);
v___x_1867_ = lean_usize_shift_right(v_x_1828_, v___x_1866_);
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = lean_usize_add(v_x_1829_, v___x_1868_);
v___x_1870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_node_1862_, v___x_1867_, v___x_1869_, v_x_1830_, v_x_1831_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1870_);
v___x_1872_ = v___x_1864_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
v___y_1845_ = v___x_1872_;
goto v___jp_1844_;
}
}
}
default: 
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_x_1830_);
lean_ctor_set(v___x_1875_, 1, v_x_1831_);
v___y_1845_ = v___x_1875_;
goto v___jp_1844_;
}
}
v___jp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_array_fset(v_xs_x27_1843_, v_j_1835_, v___y_1845_);
lean_dec(v_j_1835_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1846_);
v___x_1848_ = v___x_1839_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
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
lean_object* v_ks_1878_; lean_object* v_vs_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1897_; 
v_ks_1878_ = lean_ctor_get(v_x_1827_, 0);
v_vs_1879_ = lean_ctor_get(v_x_1827_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_x_1827_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1881_ = v_x_1827_;
v_isShared_1882_ = v_isSharedCheck_1897_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_vs_1879_);
lean_inc(v_ks_1878_);
lean_dec(v_x_1827_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1897_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_ks_1878_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_vs_1879_);
v___x_1884_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v_newNode_1885_; size_t v___x_1886_; uint8_t v___x_1887_; 
v_newNode_1885_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v___x_1884_, v_x_1830_, v_x_1831_);
v___x_1886_ = ((size_t)7ULL);
v___x_1887_ = lean_usize_dec_le(v___x_1886_, v_x_1829_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1885_);
v___x_1889_ = lean_unsigned_to_nat(4u);
v___x_1890_ = lean_nat_dec_lt(v___x_1888_, v___x_1889_);
lean_dec(v___x_1888_);
if (v___x_1890_ == 0)
{
lean_object* v_ks_1891_; lean_object* v_vs_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_ks_1891_ = lean_ctor_get(v_newNode_1885_, 0);
lean_inc_ref(v_ks_1891_);
v_vs_1892_ = lean_ctor_get(v_newNode_1885_, 1);
lean_inc_ref(v_vs_1892_);
lean_dec_ref(v_newNode_1885_);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_x_1829_, v_ks_1891_, v_vs_1892_, v___x_1893_, v___x_1894_);
lean_dec_ref(v_vs_1892_);
lean_dec_ref(v_ks_1891_);
return v___x_1895_;
}
else
{
return v_newNode_1885_;
}
}
else
{
return v_newNode_1885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(size_t v_depth_1898_, lean_object* v_keys_1899_, lean_object* v_vals_1900_, lean_object* v_i_1901_, lean_object* v_entries_1902_){
_start:
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_array_get_size(v_keys_1899_);
v___x_1904_ = lean_nat_dec_lt(v_i_1901_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_dec(v_i_1901_);
return v_entries_1902_;
}
else
{
lean_object* v_k_1905_; lean_object* v_v_1906_; uint64_t v___x_1907_; size_t v_h_1908_; size_t v___x_1909_; lean_object* v___x_1910_; size_t v___x_1911_; size_t v___x_1912_; size_t v___x_1913_; size_t v_h_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_k_1905_ = lean_array_fget_borrowed(v_keys_1899_, v_i_1901_);
v_v_1906_ = lean_array_fget_borrowed(v_vals_1900_, v_i_1901_);
v___x_1907_ = l_Lean_instHashableMVarId_hash(v_k_1905_);
v_h_1908_ = lean_uint64_to_usize(v___x_1907_);
v___x_1909_ = ((size_t)5ULL);
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = ((size_t)1ULL);
v___x_1912_ = lean_usize_sub(v_depth_1898_, v___x_1911_);
v___x_1913_ = lean_usize_mul(v___x_1909_, v___x_1912_);
v_h_1914_ = lean_usize_shift_right(v_h_1908_, v___x_1913_);
v___x_1915_ = lean_nat_add(v_i_1901_, v___x_1910_);
lean_dec(v_i_1901_);
lean_inc(v_v_1906_);
lean_inc(v_k_1905_);
v___x_1916_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_entries_1902_, v_h_1914_, v_depth_1898_, v_k_1905_, v_v_1906_);
v_i_1901_ = v___x_1915_;
v_entries_1902_ = v___x_1916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_1918_, lean_object* v_keys_1919_, lean_object* v_vals_1920_, lean_object* v_i_1921_, lean_object* v_entries_1922_){
_start:
{
size_t v_depth_boxed_1923_; lean_object* v_res_1924_; 
v_depth_boxed_1923_ = lean_unbox_usize(v_depth_1918_);
lean_dec(v_depth_1918_);
v_res_1924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_boxed_1923_, v_keys_1919_, v_vals_1920_, v_i_1921_, v_entries_1922_);
lean_dec_ref(v_vals_1920_);
lean_dec_ref(v_keys_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1925_, lean_object* v_x_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_){
_start:
{
size_t v_x_7167__boxed_1930_; size_t v_x_7168__boxed_1931_; lean_object* v_res_1932_; 
v_x_7167__boxed_1930_ = lean_unbox_usize(v_x_1926_);
lean_dec(v_x_1926_);
v_x_7168__boxed_1931_ = lean_unbox_usize(v_x_1927_);
lean_dec(v_x_1927_);
v_res_1932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1925_, v_x_7167__boxed_1930_, v_x_7168__boxed_1931_, v_x_1928_, v_x_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(lean_object* v_x_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_){
_start:
{
uint64_t v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = l_Lean_instHashableMVarId_hash(v_x_1934_);
v___x_1937_ = lean_uint64_to_usize(v___x_1936_);
v___x_1938_ = ((size_t)1ULL);
v___x_1939_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1933_, v___x_1937_, v___x_1938_, v_x_1934_, v_x_1935_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(lean_object* v_range_1940_, lean_object* v_b_1941_, lean_object* v_i_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_stop_1946_; lean_object* v_step_1947_; lean_object* v_a_1949_; lean_object* v___y_1953_; uint8_t v___x_1969_; 
v_stop_1946_ = lean_ctor_get(v_range_1940_, 1);
v_step_1947_ = lean_ctor_get(v_range_1940_, 2);
v___x_1969_ = lean_nat_dec_lt(v_i_1942_, v_stop_1946_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v_i_1942_);
v___x_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_b_1941_);
return v___x_1970_;
}
else
{
lean_object* v_decls_1971_; lean_object* v_size_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v_decls_1971_ = lean_ctor_get(v_b_1941_, 1);
v_size_1972_ = lean_ctor_get(v_decls_1971_, 2);
v___x_1973_ = lean_box(0);
v___x_1974_ = lean_nat_dec_lt(v_i_1942_, v_size_1972_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = l_outOfBounds___redArg(v___x_1973_);
v___y_1953_ = v___x_1975_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1973_, v_decls_1971_, v_i_1942_);
v___y_1953_ = v___x_1976_;
goto v___jp_1952_;
}
}
v___jp_1948_:
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_nat_add(v_i_1942_, v_step_1947_);
lean_dec(v_i_1942_);
v_b_1941_ = v_a_1949_;
v_i_1942_ = v___x_1950_;
goto _start;
}
v___jp_1952_:
{
if (lean_obj_tag(v___y_1953_) == 1)
{
lean_object* v_val_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_val_1954_ = lean_ctor_get(v___y_1953_, 0);
lean_inc(v_val_1954_);
lean_dec_ref_known(v___y_1953_, 1);
v___x_1955_ = l_Lean_LocalDecl_userName(v_val_1954_);
v___x_1956_ = l_Lean_Name_hasMacroScopes(v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_Core_mkFreshUserName(v___x_1955_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = l_Lean_LocalDecl_fvarId(v_val_1954_);
lean_dec(v_val_1954_);
v___x_1960_ = l_Lean_LocalContext_setUserName(v_b_1941_, v___x_1959_, v_a_1958_);
v_a_1949_ = v___x_1960_;
goto v___jp_1948_;
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_val_1954_);
lean_dec(v_i_1942_);
lean_dec_ref(v_b_1941_);
v_a_1961_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1957_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1957_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_dec(v___x_1955_);
lean_dec(v_val_1954_);
v_a_1949_ = v_b_1941_;
goto v___jp_1948_;
}
}
else
{
lean_dec(v___y_1953_);
v_a_1949_ = v_b_1941_;
goto v___jp_1948_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_range_1977_, lean_object* v_b_1978_, lean_object* v_i_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_1977_, v_b_1978_, v_i_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v_range_1977_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(lean_object* v_lctx_1984_, lean_object* v_idx_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc_ref(v_lctx_1984_);
v___x_1993_ = lean_local_ctx_num_indices(v_lctx_1984_);
v___x_1994_ = lean_unsigned_to_nat(1u);
lean_inc(v_idx_1985_);
v___x_1995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1995_, 0, v_idx_1985_);
lean_ctor_set(v___x_1995_, 1, v___x_1993_);
lean_ctor_set(v___x_1995_, 2, v___x_1994_);
v___x_1996_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v___x_1995_, v_lctx_1984_, v_idx_1985_, v___y_1990_, v___y_1991_);
lean_dec_ref_known(v___x_1995_, 3);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0___boxed(lean_object* v_lctx_1997_, lean_object* v_idx_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_1997_, v_idx_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2006_;
}
}
static lean_object* _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__0));
v___x_2009_ = l_Lean_stringToMessageData(v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(lean_object* v_mvarId_2010_, lean_object* v_idx_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v_mctx_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_st_ref_get(v___y_2015_);
v_mctx_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_ref(v_mctx_2020_);
lean_dec(v___x_2019_);
v___x_2021_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2020_, v_mvarId_2010_);
lean_dec_ref(v_mctx_2020_);
if (lean_obj_tag(v___x_2021_) == 1)
{
lean_object* v_val_2022_; lean_object* v_userName_2023_; lean_object* v_lctx_2024_; lean_object* v_type_2025_; lean_object* v_depth_2026_; lean_object* v_localInstances_2027_; uint8_t v_kind_2028_; lean_object* v_numScopeArgs_2029_; lean_object* v_index_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2088_; 
v_val_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_val_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v_userName_2023_ = lean_ctor_get(v_val_2022_, 0);
v_lctx_2024_ = lean_ctor_get(v_val_2022_, 1);
v_type_2025_ = lean_ctor_get(v_val_2022_, 2);
v_depth_2026_ = lean_ctor_get(v_val_2022_, 3);
v_localInstances_2027_ = lean_ctor_get(v_val_2022_, 4);
v_kind_2028_ = lean_ctor_get_uint8(v_val_2022_, sizeof(void*)*7);
v_numScopeArgs_2029_ = lean_ctor_get(v_val_2022_, 5);
v_index_2030_ = lean_ctor_get(v_val_2022_, 6);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_val_2022_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2032_ = v_val_2022_;
v_isShared_2033_ = v_isSharedCheck_2088_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_index_2030_);
lean_inc(v_numScopeArgs_2029_);
lean_inc(v_localInstances_2027_);
lean_inc(v_depth_2026_);
lean_inc(v_type_2025_);
lean_inc(v_lctx_2024_);
lean_inc(v_userName_2023_);
lean_dec(v_val_2022_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2088_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_2024_, v_idx_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2079_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2079_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2079_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v_mctx_2040_; lean_object* v_cache_2041_; lean_object* v_zetaDeltaFVarIds_2042_; lean_object* v_postponed_2043_; lean_object* v_diag_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2078_; 
v___x_2039_ = lean_st_ref_take(v___y_2015_);
v_mctx_2040_ = lean_ctor_get(v___x_2039_, 0);
v_cache_2041_ = lean_ctor_get(v___x_2039_, 1);
v_zetaDeltaFVarIds_2042_ = lean_ctor_get(v___x_2039_, 2);
v_postponed_2043_ = lean_ctor_get(v___x_2039_, 3);
v_diag_2044_ = lean_ctor_get(v___x_2039_, 4);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2046_ = v___x_2039_;
v_isShared_2047_ = v_isSharedCheck_2078_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_diag_2044_);
lean_inc(v_postponed_2043_);
lean_inc(v_zetaDeltaFVarIds_2042_);
lean_inc(v_cache_2041_);
lean_inc(v_mctx_2040_);
lean_dec(v___x_2039_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2078_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_depth_2048_; lean_object* v_levelAssignDepth_2049_; lean_object* v_lmvarCounter_2050_; lean_object* v_mvarCounter_2051_; lean_object* v_lDecls_2052_; lean_object* v_decls_2053_; lean_object* v_userNames_2054_; lean_object* v_lAssignment_2055_; lean_object* v_eAssignment_2056_; lean_object* v_dAssignment_2057_; lean_object* v_synthNormMemo_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2077_; 
v_depth_2048_ = lean_ctor_get(v_mctx_2040_, 0);
v_levelAssignDepth_2049_ = lean_ctor_get(v_mctx_2040_, 1);
v_lmvarCounter_2050_ = lean_ctor_get(v_mctx_2040_, 2);
v_mvarCounter_2051_ = lean_ctor_get(v_mctx_2040_, 3);
v_lDecls_2052_ = lean_ctor_get(v_mctx_2040_, 4);
v_decls_2053_ = lean_ctor_get(v_mctx_2040_, 5);
v_userNames_2054_ = lean_ctor_get(v_mctx_2040_, 6);
v_lAssignment_2055_ = lean_ctor_get(v_mctx_2040_, 7);
v_eAssignment_2056_ = lean_ctor_get(v_mctx_2040_, 8);
v_dAssignment_2057_ = lean_ctor_get(v_mctx_2040_, 9);
v_synthNormMemo_2058_ = lean_ctor_get(v_mctx_2040_, 10);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_mctx_2040_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2060_ = v_mctx_2040_;
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_synthNormMemo_2058_);
lean_inc(v_dAssignment_2057_);
lean_inc(v_eAssignment_2056_);
lean_inc(v_lAssignment_2055_);
lean_inc(v_userNames_2054_);
lean_inc(v_decls_2053_);
lean_inc(v_lDecls_2052_);
lean_inc(v_mvarCounter_2051_);
lean_inc(v_lmvarCounter_2050_);
lean_inc(v_levelAssignDepth_2049_);
lean_inc(v_depth_2048_);
lean_dec(v_mctx_2040_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = lean_box(0);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_a_2035_);
v___x_2064_ = v___x_2032_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_userName_2023_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_a_2035_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_type_2025_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_depth_2026_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_localInstances_2027_);
lean_ctor_set(v_reuseFailAlloc_2076_, 5, v_numScopeArgs_2029_);
lean_ctor_set(v_reuseFailAlloc_2076_, 6, v_index_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2076_, sizeof(void*)*7, v_kind_2028_);
v___x_2064_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_decls_2053_, v_mvarId_2010_, v___x_2064_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 5, v___x_2065_);
v___x_2067_ = v___x_2060_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_depth_2048_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_levelAssignDepth_2049_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_lmvarCounter_2050_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_mvarCounter_2051_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_lDecls_2052_);
lean_ctor_set(v_reuseFailAlloc_2075_, 5, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 6, v_userNames_2054_);
lean_ctor_set(v_reuseFailAlloc_2075_, 7, v_lAssignment_2055_);
lean_ctor_set(v_reuseFailAlloc_2075_, 8, v_eAssignment_2056_);
lean_ctor_set(v_reuseFailAlloc_2075_, 9, v_dAssignment_2057_);
lean_ctor_set(v_reuseFailAlloc_2075_, 10, v_synthNormMemo_2058_);
v___x_2067_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2067_);
v___x_2069_ = v___x_2046_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_cache_2041_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_zetaDeltaFVarIds_2042_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_postponed_2043_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_diag_2044_);
v___x_2069_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_st_ref_put(v___y_2015_, v___x_2069_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2062_);
v___x_2072_ = v___x_2037_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2062_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
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
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_del_object(v___x_2032_);
lean_dec(v_index_2030_);
lean_dec(v_numScopeArgs_2029_);
lean_dec_ref(v_localInstances_2027_);
lean_dec(v_depth_2026_);
lean_dec_ref(v_type_2025_);
lean_dec(v_userName_2023_);
lean_dec(v_mvarId_2010_);
v_a_2080_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2034_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2034_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec(v___x_2021_);
lean_dec(v_idx_2011_);
v___x_2089_ = lean_obj_once(&l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1, &l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1_once, _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1);
v___x_2090_ = l_Lean_MessageData_ofName(v_mvarId_2010_);
v___x_2091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2091_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___boxed(lean_object* v_mvarId_2093_, lean_object* v_idx_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_mvarId_2093_, v_idx_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC(lean_object* v_goal_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_initialCtxSize_2111_; lean_object* v___x_2112_; 
v_initialCtxSize_2111_ = lean_ctor_get(v_a_2104_, 5);
lean_inc(v_initialCtxSize_2111_);
lean_inc(v_goal_2103_);
v___x_2112_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_goal_2103_, v_initialCtxSize_2111_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v___x_2113_; 
lean_dec_ref_known(v___x_2112_, 1);
lean_inc(v_goal_2103_);
v___x_2113_ = l_Lean_MVarId_getType(v_goal_2103_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = 2;
lean_inc(v_goal_2103_);
v___x_2116_ = l_Lean_MVarId_setKind___redArg(v_goal_2103_, v___x_2115_, v_a_2107_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2159_; 
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v___x_2116_, 0);
lean_dec(v_unused_2160_);
v___x_2118_ = v___x_2116_;
v_isShared_2119_ = v_isSharedCheck_2159_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v___x_2116_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2159_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v_env_2121_; uint8_t v___x_2122_; 
v___x_2120_ = lean_st_ref_get(v_a_2109_);
v_env_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc_ref(v_env_2121_);
lean_dec(v___x_2120_);
v___x_2122_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_2121_, v_a_2114_);
lean_dec(v_a_2114_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v_fuel_2124_; lean_object* v_simpState_2125_; lean_object* v_invariants_2126_; lean_object* v_vcs_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2140_; 
v___x_2123_ = lean_st_ref_take(v_a_2105_);
v_fuel_2124_ = lean_ctor_get(v___x_2123_, 0);
v_simpState_2125_ = lean_ctor_get(v___x_2123_, 1);
v_invariants_2126_ = lean_ctor_get(v___x_2123_, 2);
v_vcs_2127_ = lean_ctor_get(v___x_2123_, 3);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2129_ = v___x_2123_;
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_vcs_2127_);
lean_inc(v_invariants_2126_);
lean_inc(v_simpState_2125_);
lean_inc(v_fuel_2124_);
lean_dec(v___x_2123_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_array_push(v_vcs_2127_, v_goal_2103_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 3, v___x_2132_);
v___x_2134_ = v___x_2129_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_fuel_2124_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_simpState_2125_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_invariants_2126_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_st_ref_put(v_a_2105_, v___x_2134_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2131_);
v___x_2137_ = v___x_2118_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2131_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v___x_2141_; lean_object* v_fuel_2142_; lean_object* v_simpState_2143_; lean_object* v_invariants_2144_; lean_object* v_vcs_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2158_; 
v___x_2141_ = lean_st_ref_take(v_a_2105_);
v_fuel_2142_ = lean_ctor_get(v___x_2141_, 0);
v_simpState_2143_ = lean_ctor_get(v___x_2141_, 1);
v_invariants_2144_ = lean_ctor_get(v___x_2141_, 2);
v_vcs_2145_ = lean_ctor_get(v___x_2141_, 3);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2147_ = v___x_2141_;
v_isShared_2148_ = v_isSharedCheck_2158_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_vcs_2145_);
lean_inc(v_invariants_2144_);
lean_inc(v_simpState_2143_);
lean_inc(v_fuel_2142_);
lean_dec(v___x_2141_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2158_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_array_push(v_invariants_2144_, v_goal_2103_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 2, v___x_2150_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_fuel_2142_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_simpState_2143_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_vcs_2145_);
v___x_2152_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = lean_st_ref_put(v_a_2105_, v___x_2152_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2149_);
v___x_2155_ = v___x_2118_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2149_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2114_);
lean_dec(v_goal_2103_);
return v___x_2116_;
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_goal_2103_);
v_a_2161_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2113_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2113_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_dec(v_goal_2103_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC___boxed(lean_object* v_goal_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v_goal_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1(lean_object* v_00_u03b2_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_x_2179_, v_x_2180_, v_x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(lean_object* v_range_2183_, lean_object* v_b_2184_, lean_object* v_i_2185_, lean_object* v_hs_2186_, lean_object* v_hl_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_2183_, v_b_2184_, v_i_2185_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___boxed(lean_object* v_range_2196_, lean_object* v_b_2197_, lean_object* v_i_2198_, lean_object* v_hs_2199_, lean_object* v_hl_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(v_range_2196_, v_b_2197_, v_i_2198_, v_hs_2199_, v_hl_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_range_2196_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2209_, lean_object* v_x_2210_, size_t v_x_2211_, size_t v_x_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_2210_, v_x_2211_, v_x_2212_, v_x_2213_, v_x_2214_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_){
_start:
{
size_t v_x_7687__boxed_2222_; size_t v_x_7688__boxed_2223_; lean_object* v_res_2224_; 
v_x_7687__boxed_2222_ = lean_unbox_usize(v_x_2218_);
lean_dec(v_x_2218_);
v_x_7688__boxed_2223_ = lean_unbox_usize(v_x_2219_);
lean_dec(v_x_2219_);
v_res_2224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(v_00_u03b2_2216_, v_x_2217_, v_x_7687__boxed_2222_, v_x_7688__boxed_2223_, v_x_2220_, v_x_2221_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2225_, lean_object* v_n_2226_, lean_object* v_k_2227_, lean_object* v_v_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v_n_2226_, v_k_2227_, v_v_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2230_, size_t v_depth_2231_, lean_object* v_keys_2232_, lean_object* v_vals_2233_, lean_object* v_heq_2234_, lean_object* v_i_2235_, lean_object* v_entries_2236_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_2231_, v_keys_2232_, v_vals_2233_, v_i_2235_, v_entries_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2238_, lean_object* v_depth_2239_, lean_object* v_keys_2240_, lean_object* v_vals_2241_, lean_object* v_heq_2242_, lean_object* v_i_2243_, lean_object* v_entries_2244_){
_start:
{
size_t v_depth_boxed_2245_; lean_object* v_res_2246_; 
v_depth_boxed_2245_ = lean_unbox_usize(v_depth_2239_);
lean_dec(v_depth_2239_);
v_res_2246_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(v_00_u03b2_2238_, v_depth_boxed_2245_, v_keys_2240_, v_vals_2241_, v_heq_2242_, v_i_2243_, v_entries_2244_);
lean_dec_ref(v_vals_2241_);
lean_dec_ref(v_keys_2240_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2247_, lean_object* v_x_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2248_, v_x_2249_, v_x_2250_, v_x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC(lean_object* v_subGoal_2253_, lean_object* v_name_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_subGoal_2253_, v_name_2254_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = l_Lean_Expr_mvarId_x21(v_a_2263_);
v___x_2265_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v___x_2264_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2272_ == 0)
{
lean_object* v_unused_2273_; 
v_unused_2273_ = lean_ctor_get(v___x_2265_, 0);
lean_dec(v_unused_2273_);
v___x_2267_ = v___x_2265_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_dec(v___x_2265_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v_a_2263_);
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2263_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2263_);
v_a_2274_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2265_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2265_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC___boxed(lean_object* v_subGoal_2282_, lean_object* v_name_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Elab_Tactic_Do_emitVC(v_subGoal_2282_, v_name_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg(lean_object* v_x_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v_simpCtx_2301_; lean_object* v_simprocs_2302_; lean_object* v_fuel_2303_; lean_object* v_simpState_2304_; lean_object* v_invariants_2305_; lean_object* v_vcs_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2327_; 
v___x_2300_ = lean_st_ref_get(v_a_2294_);
v_simpCtx_2301_ = lean_ctor_get(v_a_2293_, 2);
v_simprocs_2302_ = lean_ctor_get(v_a_2293_, 3);
v_fuel_2303_ = lean_ctor_get(v___x_2300_, 0);
v_simpState_2304_ = lean_ctor_get(v___x_2300_, 1);
v_invariants_2305_ = lean_ctor_get(v___x_2300_, 2);
v_vcs_2306_ = lean_ctor_get(v___x_2300_, 3);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2308_ = v___x_2300_;
v_isShared_2309_ = v_isSharedCheck_2327_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_vcs_2306_);
lean_inc(v_invariants_2305_);
lean_inc(v_simpState_2304_);
lean_inc(v_fuel_2303_);
lean_dec(v___x_2300_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2327_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_inc_ref(v_simprocs_2302_);
v___x_2310_ = l_Lean_Meta_Simp_mkDefaultMethodsCore(v_simprocs_2302_);
v___x_2311_ = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(v___x_2310_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = lean_st_mk_ref(v_simpState_2304_);
lean_inc(v_a_2298_);
lean_inc_ref(v_a_2297_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v___x_2312_);
lean_inc_ref(v_simpCtx_2301_);
v___x_2313_ = lean_apply_8(v_x_2292_, v___x_2311_, v_simpCtx_2301_, v___x_2312_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, lean_box(0));
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2326_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2326_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2326_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2318_ = lean_st_ref_get(v___x_2312_);
lean_dec(v___x_2312_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v___x_2318_);
v___x_2320_ = v___x_2308_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_fuel_2303_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_invariants_2305_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_vcs_2306_);
v___x_2320_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_st_ref_swap(v_a_2294_, v___x_2320_);
lean_dec(v___x_2321_);
if (v_isShared_2317_ == 0)
{
v___x_2323_ = v___x_2316_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2314_);
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
else
{
lean_dec(v___x_2312_);
lean_del_object(v___x_2308_);
lean_dec_ref(v_vcs_2306_);
lean_dec_ref(v_invariants_2305_);
lean_dec(v_fuel_2303_);
return v___x_2313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg___boxed(lean_object* v_x_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM(lean_object* v_00_u03b1_2337_, lean_object* v_x_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_x_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_Elab_Tactic_Do_liftSimpM(v_00_u03b1_2347_, v_x_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(lean_object* v_00_u03b1_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_x_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(v_00_u03b1_2367_, v_x_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg(lean_object* v_jp_2379_, lean_object* v_info_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_config_2389_; lean_object* v_specThms_2390_; lean_object* v_simpCtx_2391_; lean_object* v_simprocs_2392_; lean_object* v_jps_2393_; lean_object* v_initialCtxSize_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_config_2389_ = lean_ctor_get(v_a_2382_, 0);
v_specThms_2390_ = lean_ctor_get(v_a_2382_, 1);
v_simpCtx_2391_ = lean_ctor_get(v_a_2382_, 2);
v_simprocs_2392_ = lean_ctor_get(v_a_2382_, 3);
v_jps_2393_ = lean_ctor_get(v_a_2382_, 4);
v_initialCtxSize_2394_ = lean_ctor_get(v_a_2382_, 5);
lean_inc(v_jps_2393_);
v___x_2395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_jp_2379_, v_info_2380_, v_jps_2393_);
lean_inc(v_initialCtxSize_2394_);
lean_inc_ref(v_simprocs_2392_);
lean_inc_ref(v_simpCtx_2391_);
lean_inc_ref(v_specThms_2390_);
lean_inc_ref(v_config_2389_);
v___x_2396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2396_, 0, v_config_2389_);
lean_ctor_set(v___x_2396_, 1, v_specThms_2390_);
lean_ctor_set(v___x_2396_, 2, v_simpCtx_2391_);
lean_ctor_set(v___x_2396_, 3, v_simprocs_2392_);
lean_ctor_set(v___x_2396_, 4, v___x_2395_);
lean_ctor_set(v___x_2396_, 5, v_initialCtxSize_2394_);
lean_inc(v_a_2387_);
lean_inc_ref(v_a_2386_);
lean_inc(v_a_2385_);
lean_inc_ref(v_a_2384_);
lean_inc(v_a_2383_);
v___x_2397_ = lean_apply_7(v_a_2381_, v___x_2396_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, lean_box(0));
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg___boxed(lean_object* v_jp_2398_, lean_object* v_info_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_2398_, v_info_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP(lean_object* v_00_u03b1_2409_, lean_object* v_jp_2410_, lean_object* v_info_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_2410_, v_info_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_jp_2422_, lean_object* v_info_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Elab_Tactic_Do_withJP(v_00_u03b1_2421_, v_jp_2422_, v_info_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(lean_object* v_t_2433_, lean_object* v_k_2434_){
_start:
{
if (lean_obj_tag(v_t_2433_) == 0)
{
lean_object* v_k_2435_; lean_object* v_v_2436_; lean_object* v_l_2437_; lean_object* v_r_2438_; uint8_t v___x_2439_; 
v_k_2435_ = lean_ctor_get(v_t_2433_, 1);
v_v_2436_ = lean_ctor_get(v_t_2433_, 2);
v_l_2437_ = lean_ctor_get(v_t_2433_, 3);
v_r_2438_ = lean_ctor_get(v_t_2433_, 4);
v___x_2439_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2434_, v_k_2435_);
switch(v___x_2439_)
{
case 0:
{
v_t_2433_ = v_l_2437_;
goto _start;
}
case 1:
{
lean_object* v___x_2441_; 
lean_inc(v_v_2436_);
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_v_2436_);
return v___x_2441_;
}
default: 
{
v_t_2433_ = v_r_2438_;
goto _start;
}
}
}
else
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_box(0);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_2444_, lean_object* v_k_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_2444_, v_k_2445_);
lean_dec(v_k_2445_);
lean_dec(v_t_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(lean_object* v_jp_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_jps_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_jps_2450_ = lean_ctor_get(v_a_2448_, 4);
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_jps_2450_, v_jp_2447_);
v___x_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg___boxed(lean_object* v_jp_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_2453_, v_a_2454_);
lean_dec_ref(v_a_2454_);
lean_dec(v_jp_2453_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f(lean_object* v_jp_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_2457_, v_a_2458_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___boxed(lean_object* v_jp_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Elab_Tactic_Do_knownJP_x3f(v_jp_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_jp_2466_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(lean_object* v_00_u03b4_2475_, lean_object* v_t_2476_, lean_object* v_k_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_2476_, v_k_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_2479_, lean_object* v_t_2480_, lean_object* v_k_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(v_00_u03b4_2479_, v_t_2480_, v_k_2481_);
lean_dec(v_k_2481_);
lean_dec(v_t_2480_);
return v_res_2482_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isDuplicable(lean_object* v_e_2488_){
_start:
{
switch(lean_obj_tag(v_e_2488_))
{
case 5:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isDuplicable___closed__2));
v___x_2490_ = l_Lean_Expr_isAppOf(v_e_2488_, v___x_2489_);
return v___x_2490_;
}
case 6:
{
uint8_t v___x_2491_; 
v___x_2491_ = 0;
return v___x_2491_;
}
case 7:
{
uint8_t v___x_2492_; 
v___x_2492_ = 0;
return v___x_2492_;
}
case 8:
{
uint8_t v___x_2493_; 
v___x_2493_ = 0;
return v___x_2493_;
}
case 10:
{
lean_object* v_expr_2494_; 
v_expr_2494_ = lean_ctor_get(v_e_2488_, 1);
v_e_2488_ = v_expr_2494_;
goto _start;
}
case 11:
{
lean_object* v_struct_2496_; 
v_struct_2496_ = lean_ctor_get(v_e_2488_, 2);
v_e_2488_ = v_struct_2496_;
goto _start;
}
default: 
{
uint8_t v___x_2498_; 
v___x_2498_ = 1;
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___boxed(lean_object* v_e_2499_){
_start:
{
uint8_t v_res_2500_; lean_object* v_r_2501_; 
v_res_2500_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_e_2499_);
lean_dec_ref(v_e_2499_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(lean_object* v_k_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v_b_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; 
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
v___x_2511_ = lean_apply_8(v_k_2502_, v_b_2505_, v___y_2503_, v___y_2504_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, lean_box(0));
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed(lean_object* v_k_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v_b_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(v_k_2512_, v___y_2513_, v___y_2514_, v_b_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(lean_object* v_name_2522_, lean_object* v_type_2523_, lean_object* v_val_2524_, lean_object* v_k_2525_, uint8_t v_nondep_2526_, uint8_t v_kind_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___f_2535_; lean_object* v___x_2536_; 
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
v___f_2535_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2535_, 0, v_k_2525_);
lean_closure_set(v___f_2535_, 1, v___y_2528_);
lean_closure_set(v___f_2535_, 2, v___y_2529_);
v___x_2536_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2522_, v_type_2523_, v_val_2524_, v___f_2535_, v_nondep_2526_, v_kind_2527_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2536_) == 0)
{
return v___x_2536_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___boxed(lean_object* v_name_2545_, lean_object* v_type_2546_, lean_object* v_val_2547_, lean_object* v_k_2548_, lean_object* v_nondep_2549_, lean_object* v_kind_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
uint8_t v_nondep_boxed_2558_; uint8_t v_kind_boxed_2559_; lean_object* v_res_2560_; 
v_nondep_boxed_2558_ = lean_unbox(v_nondep_2549_);
v_kind_boxed_2559_ = lean_unbox(v_kind_2550_);
v_res_2560_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2545_, v_type_2546_, v_val_2547_, v_k_2548_, v_nondep_boxed_2558_, v_kind_boxed_2559_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(lean_object* v_00_u03b1_2561_, lean_object* v_name_2562_, lean_object* v_type_2563_, lean_object* v_val_2564_, lean_object* v_k_2565_, uint8_t v_nondep_2566_, uint8_t v_kind_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2562_, v_type_2563_, v_val_2564_, v_k_2565_, v_nondep_2566_, v_kind_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___boxed(lean_object* v_00_u03b1_2576_, lean_object* v_name_2577_, lean_object* v_type_2578_, lean_object* v_val_2579_, lean_object* v_k_2580_, lean_object* v_nondep_2581_, lean_object* v_kind_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
uint8_t v_nondep_boxed_2590_; uint8_t v_kind_boxed_2591_; lean_object* v_res_2592_; 
v_nondep_boxed_2590_ = lean_unbox(v_nondep_2581_);
v_kind_boxed_2591_ = lean_unbox(v_kind_2582_);
v_res_2592_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(v_00_u03b1_2576_, v_name_2577_, v_type_2578_, v_val_2579_, v_k_2580_, v_nondep_boxed_2590_, v_kind_boxed_2591_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(lean_object* v___x_2593_, lean_object* v_x_2594_, uint8_t v___x_2595_, uint8_t v___x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Meta_mkLetFVars(v___x_2593_, v_x_2594_, v___x_2595_, v___x_2595_, v___x_2596_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed(lean_object* v___x_2606_, lean_object* v_x_2607_, lean_object* v___x_2608_, lean_object* v___x_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v___x_1435__boxed_2618_; uint8_t v___x_1436__boxed_2619_; lean_object* v_res_2620_; 
v___x_1435__boxed_2618_ = lean_unbox(v___x_2608_);
v___x_1436__boxed_2619_ = lean_unbox(v___x_2609_);
v_res_2620_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(v___x_2606_, v_x_2607_, v___x_1435__boxed_2618_, v___x_1436__boxed_2619_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___x_2606_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(lean_object* v_fv_2621_, uint8_t v___x_2622_, lean_object* v_x_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___f_2637_; lean_object* v___x_2638_; 
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_mk_empty_array_with_capacity(v___x_2631_);
v___x_2633_ = lean_array_push(v___x_2632_, v_fv_2621_);
v___x_2634_ = 1;
v___x_2635_ = lean_box(v___x_2622_);
v___x_2636_ = lean_box(v___x_2634_);
v___f_2637_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_2637_, 0, v___x_2633_);
lean_closure_set(v___f_2637_, 1, v_x_2623_);
lean_closure_set(v___f_2637_, 2, v___x_2635_);
lean_closure_set(v___f_2637_, 3, v___x_2636_);
v___x_2638_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_2637_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed(lean_object* v_fv_2639_, lean_object* v___x_2640_, lean_object* v_x_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
uint8_t v___x_1471__boxed_2649_; lean_object* v_res_2650_; 
v___x_1471__boxed_2649_ = lean_unbox(v___x_2640_);
v_res_2650_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(v_fv_2639_, v___x_1471__boxed_2649_, v_x_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(uint8_t v___x_2651_, lean_object* v_k_2652_, lean_object* v_fv_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = lean_box(v___x_2651_);
lean_inc_ref(v_fv_2653_);
v___f_2662_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2662_, 0, v_fv_2653_);
lean_closure_set(v___f_2662_, 1, v___x_2661_);
v___x_2663_ = lean_box(v___x_2651_);
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2654_);
v___x_2664_ = lean_apply_10(v_k_2652_, v___x_2663_, v_fv_2653_, v___f_2662_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed(lean_object* v___x_2665_, lean_object* v_k_2666_, lean_object* v_fv_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v___x_1514__boxed_2675_; lean_object* v_res_2676_; 
v___x_1514__boxed_2675_ = lean_unbox(v___x_2665_);
v_res_2676_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(v___x_1514__boxed_2675_, v_k_2666_, v_fv_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___y_2677_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3___boxed(lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(lean_object* v_name_2696_, lean_object* v_type_2697_, lean_object* v_val_2698_, lean_object* v_k_2699_, uint8_t v_kind_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
uint8_t v___x_2708_; 
v___x_2708_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_val_2698_);
if (v___x_2708_ == 0)
{
uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; 
v___x_2709_ = 1;
v___x_2710_ = lean_box(v___x_2709_);
v___f_2711_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed), 10, 2);
lean_closure_set(v___f_2711_, 0, v___x_2710_);
lean_closure_set(v___f_2711_, 1, v_k_2699_);
v___x_2712_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2696_, v_type_2697_, v_val_2698_, v___f_2711_, v___x_2708_, v_kind_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
return v___x_2712_;
}
else
{
lean_object* v___f_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec_ref(v_type_2697_);
lean_dec(v_name_2696_);
v___f_2713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___closed__0));
v___x_2714_ = 0;
v___x_2715_ = lean_box(v___x_2714_);
lean_inc(v_a_2706_);
lean_inc_ref(v_a_2705_);
lean_inc(v_a_2704_);
lean_inc_ref(v_a_2703_);
lean_inc(v_a_2702_);
lean_inc_ref(v_a_2701_);
v___x_2716_ = lean_apply_10(v_k_2699_, v___x_2715_, v_val_2698_, v___f_2713_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, lean_box(0));
return v___x_2716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___boxed(lean_object* v_name_2717_, lean_object* v_type_2718_, lean_object* v_val_2719_, lean_object* v_k_2720_, lean_object* v_kind_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
uint8_t v_kind_boxed_2729_; lean_object* v_res_2730_; 
v_kind_boxed_2729_ = lean_unbox(v_kind_2721_);
v_res_2730_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2717_, v_type_2718_, v_val_2719_, v_k_2720_, v_kind_boxed_2729_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared(lean_object* v_00_u03b1_2731_, lean_object* v_name_2732_, lean_object* v_type_2733_, lean_object* v_val_2734_, lean_object* v_k_2735_, uint8_t v_kind_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2732_, v_type_2733_, v_val_2734_, v_k_2735_, v_kind_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_name_2746_, lean_object* v_type_2747_, lean_object* v_val_2748_, lean_object* v_k_2749_, lean_object* v_kind_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
uint8_t v_kind_boxed_2758_; lean_object* v_res_2759_; 
v_kind_boxed_2758_ = lean_unbox(v_kind_2750_);
v_res_2759_ = l_Lean_Elab_Tactic_Do_withLetDeclShared(v_00_u03b1_2745_, v_name_2746_, v_type_2747_, v_val_2748_, v_k_2749_, v_kind_boxed_2758_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
return v_res_2759_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object* v_n_2763_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = l_Lean_Name_eraseMacroScopes(v_n_2763_);
v___x_2765_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isJP___closed__1));
v___x_2766_ = lean_name_eq(v___x_2764_, v___x_2765_);
lean_dec(v___x_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isJP___boxed(lean_object* v_n_2767_){
_start:
{
uint8_t v_res_2768_; lean_object* v_r_2769_; 
v_res_2768_ = l_Lean_Elab_Tactic_Do_isJP(v_n_2767_);
lean_dec(v_n_2767_);
v_r_2769_ = lean_box(v_res_2768_);
return v_r_2769_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__0));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams(lean_object* v_joinTy_2773_, lean_object* v_resTy_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
uint8_t v___x_2780_; 
v___x_2780_ = l_Lean_Expr_isMData(v_joinTy_2773_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_expr_eqv(v_joinTy_2773_, v_resTy_2774_);
if (v___x_2781_ == 0)
{
uint8_t v___x_2782_; 
v___x_2782_ = l_Lean_Expr_isForall(v_joinTy_2773_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2783_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1, &l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1_once, _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1);
v___x_2784_ = l_Lean_MessageData_ofExpr(v_joinTy_2773_);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2785_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = l_Lean_Expr_consumeMData(v_joinTy_2773_);
lean_dec_ref(v_joinTy_2773_);
v___x_2788_ = l_Lean_Expr_bindingBody_x21(v___x_2787_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v___x_2788_, v_resTy_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2799_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_nat_add(v___x_2794_, v_a_2790_);
lean_dec(v_a_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2795_);
v___x_2797_ = v___x_2792_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
else
{
return v___x_2789_;
}
}
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec_ref(v_joinTy_2773_);
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
}
else
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_Expr_consumeMData(v_joinTy_2773_);
lean_dec_ref(v_joinTy_2773_);
v_joinTy_2773_ = v___x_2802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams___boxed(lean_object* v_joinTy_2804_, lean_object* v_resTy_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v_joinTy_2804_, v_resTy_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec_ref(v_resTy_2805_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(lean_object* v_lastReduction_2813_, lean_object* v_f_2814_, lean_object* v_rargs_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
switch(lean_obj_tag(v_f_2814_))
{
case 10:
{
lean_object* v_expr_2821_; 
v_expr_2821_ = lean_ctor_get(v_f_2814_, 1);
lean_inc_ref(v_expr_2821_);
lean_dec_ref_known(v_f_2814_, 2);
v_f_2814_ = v_expr_2821_;
goto _start;
}
case 5:
{
lean_object* v_fn_2823_; lean_object* v_arg_2824_; lean_object* v___x_2825_; 
v_fn_2823_ = lean_ctor_get(v_f_2814_, 0);
lean_inc_ref(v_fn_2823_);
v_arg_2824_ = lean_ctor_get(v_f_2814_, 1);
lean_inc_ref(v_arg_2824_);
lean_dec_ref_known(v_f_2814_, 2);
v___x_2825_ = lean_array_push(v_rargs_2815_, v_arg_2824_);
v_f_2814_ = v_fn_2823_;
v_rargs_2815_ = v___x_2825_;
goto _start;
}
case 6:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2827_ = lean_array_get_size(v_rargs_2815_);
v___x_2828_ = lean_unsigned_to_nat(0u);
v___x_2829_ = lean_nat_dec_eq(v___x_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_object* v_e_x27_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec(v_lastReduction_2813_);
v_e_x27_2830_ = l_Lean_Expr_betaRev(v_f_2814_, v_rargs_2815_, v___x_2829_, v___x_2829_);
lean_dec_ref(v_rargs_2815_);
lean_inc_ref(v_e_x27_2830_);
v___x_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_e_x27_2830_);
v___x_2832_ = l_Lean_Expr_getAppFn(v_e_x27_2830_);
v___x_2833_ = l_Lean_Expr_getAppNumArgs(v_e_x27_2830_);
v___x_2834_ = lean_mk_empty_array_with_capacity(v___x_2833_);
lean_dec(v___x_2833_);
v___x_2835_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_x27_2830_, v___x_2834_);
v_lastReduction_2813_ = v___x_2831_;
v_f_2814_ = v___x_2832_;
v_rargs_2815_ = v___x_2835_;
goto _start;
}
else
{
lean_object* v___x_2837_; 
lean_dec_ref_known(v_f_2814_, 3);
lean_dec_ref(v_rargs_2815_);
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v_lastReduction_2813_);
return v___x_2837_;
}
}
case 4:
{
lean_object* v_declName_2838_; lean_object* v___x_2839_; lean_object* v_env_2840_; lean_object* v___x_2841_; 
v_declName_2838_ = lean_ctor_get(v_f_2814_, 0);
v___x_2839_ = lean_st_ref_get(v_a_2819_);
v_env_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc_ref(v_env_2840_);
lean_dec(v___x_2839_);
lean_inc(v_declName_2838_);
v___x_2841_ = l_Lean_Environment_getProjectionStructureName_x3f(v_env_2840_, v_declName_2838_);
if (lean_obj_tag(v___x_2841_) == 1)
{
lean_object* v_val_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2876_; 
v_val_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2876_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_val_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2876_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
if (lean_obj_tag(v_val_2842_) == 1)
{
lean_object* v_pre_2846_; 
v_pre_2846_ = lean_ctor_get(v_val_2842_, 0);
if (lean_obj_tag(v_pre_2846_) == 0)
{
lean_object* v_str_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_str_2847_ = lean_ctor_get(v_val_2842_, 1);
lean_inc_ref(v_str_2847_);
lean_dec_ref_known(v_val_2842_, 2);
v___x_2848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___closed__0));
v___x_2849_ = lean_string_dec_eq(v_str_2847_, v___x_2848_);
lean_dec_ref(v_str_2847_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2851_; 
lean_dec_ref_known(v_f_2814_, 2);
lean_dec_ref(v_rargs_2815_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 0);
lean_ctor_set(v___x_2844_, 0, v_lastReduction_2813_);
v___x_2851_ = v___x_2844_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_lastReduction_2813_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
else
{
lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; 
lean_del_object(v___x_2844_);
v___x_2853_ = l_Lean_mkAppRev(v_f_2814_, v_rargs_2815_);
lean_dec_ref(v_rargs_2815_);
v___x_2854_ = 0;
v___x_2855_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_2853_, v___x_2854_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2869_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2869_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2869_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
if (lean_obj_tag(v_a_2856_) == 0)
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v_lastReduction_2813_);
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_lastReduction_2813_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
else
{
lean_object* v_val_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_del_object(v___x_2858_);
v_val_2863_ = lean_ctor_get(v_a_2856_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v_a_2856_, 1);
v___x_2864_ = l_Lean_Expr_getAppFn(v_val_2863_);
v___x_2865_ = l_Lean_Expr_getAppNumArgs(v_val_2863_);
v___x_2866_ = lean_mk_empty_array_with_capacity(v___x_2865_);
lean_dec(v___x_2865_);
v___x_2867_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_val_2863_, v___x_2866_);
v_f_2814_ = v___x_2864_;
v_rargs_2815_ = v___x_2867_;
goto _start;
}
}
}
else
{
lean_dec(v_lastReduction_2813_);
return v___x_2855_;
}
}
}
else
{
lean_object* v___x_2871_; 
lean_dec_ref_known(v_val_2842_, 2);
lean_dec_ref_known(v_f_2814_, 2);
lean_dec_ref(v_rargs_2815_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 0);
lean_ctor_set(v___x_2844_, 0, v_lastReduction_2813_);
v___x_2871_ = v___x_2844_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_lastReduction_2813_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
else
{
lean_object* v___x_2874_; 
lean_dec(v_val_2842_);
lean_dec_ref_known(v_f_2814_, 2);
lean_dec_ref(v_rargs_2815_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 0);
lean_ctor_set(v___x_2844_, 0, v_lastReduction_2813_);
v___x_2874_ = v___x_2844_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_lastReduction_2813_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v___x_2877_; 
lean_dec(v___x_2841_);
lean_dec_ref_known(v_f_2814_, 2);
lean_dec_ref(v_rargs_2815_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v_lastReduction_2813_);
return v___x_2877_;
}
}
case 11:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_Meta_reduceProj_x3f(v_f_2814_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2900_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2900_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2900_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
if (lean_obj_tag(v_a_2879_) == 0)
{
lean_object* v___x_2884_; 
lean_dec_ref(v_rargs_2815_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v_lastReduction_2813_);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_lastReduction_2813_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
else
{
lean_object* v_val_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2899_; 
lean_del_object(v___x_2881_);
lean_dec(v_lastReduction_2813_);
v_val_2886_ = lean_ctor_get(v_a_2879_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_a_2879_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2888_ = v_a_2879_;
v_isShared_2889_ = v_isSharedCheck_2899_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_val_2886_);
lean_dec(v_a_2879_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2899_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = l_Lean_mkAppRev(v_val_2886_, v_rargs_2815_);
lean_dec_ref(v_rargs_2815_);
lean_inc_ref(v___x_2890_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2893_ = l_Lean_Expr_getAppFn(v___x_2890_);
v___x_2894_ = l_Lean_Expr_getAppNumArgs(v___x_2890_);
v___x_2895_ = lean_mk_empty_array_with_capacity(v___x_2894_);
lean_dec(v___x_2894_);
v___x_2896_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2890_, v___x_2895_);
v_lastReduction_2813_ = v___x_2892_;
v_f_2814_ = v___x_2893_;
v_rargs_2815_ = v___x_2896_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v_rargs_2815_);
lean_dec(v_lastReduction_2813_);
return v___x_2878_;
}
}
case 8:
{
lean_object* v_declName_2901_; lean_object* v_type_2902_; lean_object* v_value_2903_; lean_object* v_body_2904_; uint8_t v_nondep_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_declName_2901_ = lean_ctor_get(v_f_2814_, 0);
lean_inc(v_declName_2901_);
v_type_2902_ = lean_ctor_get(v_f_2814_, 1);
lean_inc_ref(v_type_2902_);
v_value_2903_ = lean_ctor_get(v_f_2814_, 2);
lean_inc_ref(v_value_2903_);
v_body_2904_ = lean_ctor_get(v_f_2814_, 3);
lean_inc_ref(v_body_2904_);
v_nondep_2905_ = lean_ctor_get_uint8(v_f_2814_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_f_2814_, 4);
v___x_2906_ = lean_box(0);
v___x_2907_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_2906_, v_body_2904_, v_rargs_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2927_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2927_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2927_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
if (lean_obj_tag(v_a_2908_) == 0)
{
lean_object* v___x_2913_; 
lean_dec_ref(v_value_2903_);
lean_dec_ref(v_type_2902_);
lean_dec(v_declName_2901_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v_lastReduction_2813_);
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_lastReduction_2813_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
else
{
lean_object* v_val_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_lastReduction_2813_);
v_val_2915_ = lean_ctor_get(v_a_2908_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2908_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2917_ = v_a_2908_;
v_isShared_2918_ = v_isSharedCheck_2926_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_val_2915_);
lean_dec(v_a_2908_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2926_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2919_ = l_Lean_Expr_letE___override(v_declName_2901_, v_type_2902_, v_value_2903_, v_val_2915_, v_nondep_2905_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2919_);
v___x_2921_ = v___x_2917_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2923_; 
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2921_);
v___x_2923_ = v___x_2910_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_2903_);
lean_dec_ref(v_type_2902_);
lean_dec(v_declName_2901_);
lean_dec(v_lastReduction_2813_);
return v___x_2907_;
}
}
default: 
{
lean_object* v___x_2928_; 
lean_dec_ref(v_rargs_2815_);
lean_dec_ref(v_f_2814_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_lastReduction_2813_);
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___boxed(lean_object* v_lastReduction_2929_, lean_object* v_f_2930_, lean_object* v_rargs_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v_lastReduction_2929_, v_f_2930_, v_rargs_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(lean_object* v_e_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = l_Lean_Expr_getAppFn(v_e_2938_);
v___x_2946_ = l_Lean_Expr_getAppNumArgs(v_e_2938_);
v___x_2947_ = lean_mk_empty_array_with_capacity(v___x_2946_);
lean_dec(v___x_2946_);
v___x_2948_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_2938_, v___x_2947_);
v___x_2949_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_2944_, v___x_2945_, v___x_2948_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f___boxed(lean_object* v_e_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(v_e_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
return v_res_2956_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = lean_box(0);
v___x_2958_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2957_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg(){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___boxed(lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(lean_object* v_00_u03b1_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___boxed(lean_object* v_00_u03b1_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(v_00_u03b1_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(lean_object* v_as_2987_, size_t v_sz_2988_, size_t v_i_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_a_3000_; uint8_t v___x_3004_; 
v___x_3004_ = lean_usize_dec_lt(v_i_2989_, v_sz_2988_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v_b_2990_);
return v___x_3005_;
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_a_3006_ = lean_array_uget_borrowed(v_as_2987_, v_i_2989_);
lean_inc(v_a_3006_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_a_3006_);
v___x_3008_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_b_2990_, v___x_3007_);
lean_dec_ref_known(v___x_3007_, 1);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_unsigned_to_nat(1000u);
v___x_3010_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2991_, v___y_2993_, v___y_2995_, v___y_2997_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
lean_inc(v_a_3006_);
v___x_3012_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_a_3006_, v___x_3009_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
lean_dec(v_a_3011_);
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_b_2990_, v_a_3013_);
v_a_3000_ = v___x_3014_;
goto v___jp_2999_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3036_; 
v_a_3015_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3017_ = v___x_3012_;
v_isShared_3018_ = v_isSharedCheck_3036_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3012_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3036_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
uint8_t v___x_3019_; 
v___x_3019_ = l_Lean_Exception_isInterrupt(v_a_3015_);
if (v___x_3019_ == 0)
{
uint8_t v___x_3020_; 
lean_inc(v_a_3015_);
v___x_3020_ = l_Lean_Exception_isRuntime(v_a_3015_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
lean_del_object(v___x_3017_);
lean_dec(v_a_3015_);
v___x_3021_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3011_, v___x_3020_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_dec_ref_known(v___x_3021_, 1);
v_a_3000_ = v_b_2990_;
goto v___jp_2999_;
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec_ref(v_b_2990_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v___x_3031_; 
lean_dec(v_a_3011_);
lean_dec_ref(v_b_2990_);
if (v_isShared_3018_ == 0)
{
v___x_3031_ = v___x_3017_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3015_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
else
{
lean_object* v___x_3034_; 
lean_dec(v_a_3011_);
lean_dec_ref(v_b_2990_);
if (v_isShared_3018_ == 0)
{
v___x_3034_ = v___x_3017_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3015_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v_b_2990_);
v_a_3037_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3010_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3010_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
v_a_3000_ = v_b_2990_;
goto v___jp_2999_;
}
}
v___jp_2999_:
{
size_t v___x_3001_; size_t v___x_3002_; 
v___x_3001_ = ((size_t)1ULL);
v___x_3002_ = lean_usize_add(v_i_2989_, v___x_3001_);
v_i_2989_ = v___x_3002_;
v_b_2990_ = v_a_3000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg___boxed(lean_object* v_as_3045_, lean_object* v_sz_3046_, lean_object* v_i_3047_, lean_object* v_b_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
size_t v_sz_boxed_3057_; size_t v_i_boxed_3058_; lean_object* v_res_3059_; 
v_sz_boxed_3057_ = lean_unbox_usize(v_sz_3046_);
lean_dec(v_sz_3046_);
v_i_boxed_3058_ = lean_unbox_usize(v_i_3047_);
lean_dec(v_i_3047_);
v_res_3059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_3045_, v_sz_boxed_3057_, v_i_boxed_3058_, v_b_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v_as_3045_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(lean_object* v_msg_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_ref_3066_; lean_object* v___x_3067_; lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3076_; 
v_ref_3066_ = lean_ctor_get(v___y_3063_, 2);
v___x_3067_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_inc(v_ref_3066_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_ref_3066_);
lean_ctor_set(v___x_3072_, 1, v_a_3068_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 1);
lean_ctor_set(v___x_3070_, 0, v___x_3072_);
v___x_3074_ = v___x_3070_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg___boxed(lean_object* v_msg_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(lean_object* v_ref_3084_, lean_object* v_msg_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_toCold_3095_; lean_object* v_currRecDepth_3096_; lean_object* v_ref_3097_; uint16_t v_optionFlags_3098_; uint8_t v_suppressElabErrors_3099_; uint8_t v_isRecordingDeps_3100_; lean_object* v_ref_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_toCold_3095_ = lean_ctor_get(v___y_3092_, 0);
v_currRecDepth_3096_ = lean_ctor_get(v___y_3092_, 1);
v_ref_3097_ = lean_ctor_get(v___y_3092_, 2);
v_optionFlags_3098_ = lean_ctor_get_uint16(v___y_3092_, sizeof(void*)*3);
v_suppressElabErrors_3099_ = lean_ctor_get_uint8(v___y_3092_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3100_ = lean_ctor_get_uint8(v___y_3092_, sizeof(void*)*3 + 3);
v_ref_3101_ = l_Lean_replaceRef(v_ref_3084_, v_ref_3097_);
lean_inc(v_currRecDepth_3096_);
lean_inc_ref(v_toCold_3095_);
v___x_3102_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3102_, 0, v_toCold_3095_);
lean_ctor_set(v___x_3102_, 1, v_currRecDepth_3096_);
lean_ctor_set(v___x_3102_, 2, v_ref_3101_);
lean_ctor_set_uint16(v___x_3102_, sizeof(void*)*3, v_optionFlags_3098_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*3 + 2, v_suppressElabErrors_3099_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*3 + 3, v_isRecordingDeps_3100_);
v___x_3103_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3085_, v___y_3090_, v___y_3091_, v___x_3102_, v___y_3093_);
lean_dec_ref_known(v___x_3102_, 3);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_ref_3104_, lean_object* v_msg_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3104_, v_msg_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v_ref_3104_);
return v_res_3115_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0);
v___x_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3119_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_3121_ = lean_unsigned_to_nat(0u);
v___x_3122_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
lean_ctor_set(v___x_3122_, 2, v___x_3121_);
lean_ctor_set(v___x_3122_, 3, v___x_3121_);
lean_ctor_set(v___x_3122_, 4, v___x_3120_);
lean_ctor_set(v___x_3122_, 5, v___x_3120_);
lean_ctor_set(v___x_3122_, 6, v___x_3120_);
lean_ctor_set(v___x_3122_, 7, v___x_3120_);
lean_ctor_set(v___x_3122_, 8, v___x_3120_);
lean_ctor_set(v___x_3122_, 9, v___x_3120_);
lean_ctor_set(v___x_3122_, 10, v___x_3119_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = lean_unsigned_to_nat(32u);
v___x_3124_ = lean_mk_empty_array_with_capacity(v___x_3123_);
v___x_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
return v___x_3125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3126_ = ((size_t)5ULL);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_unsigned_to_nat(32u);
v___x_3129_ = lean_mk_empty_array_with_capacity(v___x_3128_);
v___x_3130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3);
v___x_3131_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3129_);
lean_ctor_set(v___x_3131_, 2, v___x_3127_);
lean_ctor_set(v___x_3131_, 3, v___x_3127_);
lean_ctor_set_usize(v___x_3131_, 4, v___x_3126_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3132_ = lean_box(1);
v___x_3133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4);
v___x_3134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_3135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v___x_3133_);
lean_ctor_set(v___x_3135_, 2, v___x_3132_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__6));
v___x_3138_ = l_Lean_stringToMessageData(v___x_3137_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__8));
v___x_3141_ = l_Lean_stringToMessageData(v___x_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__10));
v___x_3144_ = l_Lean_stringToMessageData(v___x_3143_);
return v___x_3144_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__12));
v___x_3147_ = l_Lean_stringToMessageData(v___x_3146_);
return v___x_3147_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__14));
v___x_3150_ = l_Lean_stringToMessageData(v___x_3149_);
return v___x_3150_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16));
v___x_3153_ = l_Lean_stringToMessageData(v___x_3152_);
return v___x_3153_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18));
v___x_3156_ = l_Lean_stringToMessageData(v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object* v_msg_3157_, lean_object* v_declHint_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_env_3163_; uint8_t v___x_3164_; 
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_st_ref_get(v___y_3159_);
v_env_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref(v_env_3163_);
lean_dec(v___x_3162_);
v___x_3164_ = l_Lean_Name_isAnonymous(v_declHint_3158_);
if (v___x_3164_ == 0)
{
uint8_t v_isExporting_3165_; 
v_isExporting_3165_ = lean_ctor_get_uint8(v_env_3163_, sizeof(void*)*13);
if (v_isExporting_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v_env_3163_);
lean_dec(v_declHint_3158_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_msg_3157_);
return v___x_3166_;
}
else
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
lean_inc_ref(v_env_3163_);
v___x_3167_ = l_Lean_Environment_setExporting(v_env_3163_, v___x_3164_);
lean_inc(v_declHint_3158_);
lean_inc_ref(v___x_3167_);
v___x_3168_ = l_Lean_Environment_contains(v___x_3167_, v_declHint_3158_, v_isExporting_3165_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
lean_dec_ref(v___x_3167_);
lean_dec_ref(v_env_3163_);
lean_dec(v_declHint_3158_);
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_msg_3157_);
return v___x_3169_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v_c_3175_; lean_object* v___x_3176_; 
v___x_3170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2);
v___x_3171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5);
v___x_3172_ = l_Lean_Options_empty;
v___x_3173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3167_);
lean_ctor_set(v___x_3173_, 1, v___x_3170_);
lean_ctor_set(v___x_3173_, 2, v___x_3171_);
lean_ctor_set(v___x_3173_, 3, v___x_3172_);
lean_inc(v_declHint_3158_);
v___x_3174_ = l_Lean_MessageData_ofConstName(v_declHint_3158_, v___x_3164_);
v_c_3175_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3175_, 0, v___x_3173_);
lean_ctor_set(v_c_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3163_, v_declHint_3158_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_dec_ref(v_env_3163_);
lean_dec(v_declHint_3158_);
v___x_3177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_3178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v_c_3175_);
v___x_3179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9);
v___x_3180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = l_Lean_MessageData_note(v___x_3180_);
v___x_3182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3182_, 0, v_msg_3157_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
else
{
lean_object* v_val_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3218_; 
v_val_3184_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3186_ = v___x_3176_;
v_isShared_3187_ = v_isSharedCheck_3218_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_val_3184_);
lean_dec(v___x_3176_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3218_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v_moduleNames_3189_; lean_object* v_mod_3190_; uint8_t v___x_3191_; 
v___x_3188_ = l_Lean_Environment_header(v_env_3163_);
lean_dec_ref(v_env_3163_);
v_moduleNames_3189_ = lean_ctor_get(v___x_3188_, 4);
lean_inc_ref(v_moduleNames_3189_);
lean_dec_ref(v___x_3188_);
v_mod_3190_ = lean_array_get(v___x_3161_, v_moduleNames_3189_, v_val_3184_);
lean_dec(v_val_3184_);
lean_dec_ref(v_moduleNames_3189_);
v___x_3191_ = l_Lean_isPrivateName(v_declHint_3158_);
lean_dec(v_declHint_3158_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3192_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11);
v___x_3193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
lean_ctor_set(v___x_3193_, 1, v_c_3175_);
v___x_3194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13);
v___x_3195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3193_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_MessageData_ofName(v_mod_3190_);
v___x_3197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15);
v___x_3199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3197_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = l_Lean_MessageData_note(v___x_3199_);
v___x_3201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_msg_3157_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set_tag(v___x_3186_, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3201_);
v___x_3203_ = v___x_3186_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_3206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v_c_3175_);
v___x_3207_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17);
v___x_3208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = l_Lean_MessageData_ofName(v_mod_3190_);
v___x_3210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3208_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = l_Lean_MessageData_note(v___x_3212_);
v___x_3214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_msg_3157_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set_tag(v___x_3186_, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3214_);
v___x_3216_ = v___x_3186_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3219_; 
lean_dec_ref(v_env_3163_);
lean_dec(v_declHint_3158_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v_msg_3157_);
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_msg_3220_, lean_object* v_declHint_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3220_, v_declHint_3221_, v___y_3222_);
lean_dec(v___y_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(lean_object* v_msg_3225_, lean_object* v_declHint_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___x_3236_; lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3246_; 
v___x_3236_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3225_, v_declHint_3226_, v___y_3234_);
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3246_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3246_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3241_ = l_Lean_unknownIdentifierMessageTag;
v___x_3242_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v_a_3237_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3242_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_msg_3247_, lean_object* v_declHint_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_3247_, v_declHint_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3259_, lean_object* v_msg_3260_, lean_object* v_declHint_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; lean_object* v_a_3272_; lean_object* v___x_3273_; 
v___x_3271_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_3260_, v_declHint_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3259_, v_a_3272_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3274_, lean_object* v_msg_3275_, lean_object* v_declHint_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3274_, v_msg_3275_, v_declHint_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v_ref_3274_);
return v_res_3286_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__0));
v___x_3289_ = l_Lean_stringToMessageData(v___x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(lean_object* v_ref_3290_, lean_object* v_constName_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; uint8_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3301_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1);
v___x_3302_ = 0;
lean_inc(v_constName_3291_);
v___x_3303_ = l_Lean_MessageData_ofConstName(v_constName_3291_, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3301_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3290_, v___x_3306_, v_constName_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___boxed(lean_object* v_ref_3308_, lean_object* v_constName_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3308_, v_constName_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v_ref_3308_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(lean_object* v_constName_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_ref_3330_; lean_object* v___x_3331_; 
v_ref_3330_ = lean_ctor_get(v___y_3327_, 2);
v___x_3331_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3330_, v_constName_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg___boxed(lean_object* v_constName_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(lean_object* v_fst_3343_, lean_object* v_fst_3344_, lean_object* v_specThm_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_proof_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_proof_3355_ = lean_ctor_get(v_specThm_3345_, 2);
lean_inc_ref(v_proof_3355_);
lean_dec_ref(v_specThm_3345_);
v___x_3356_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(v_fst_3343_, v_proof_3355_);
v___x_3357_ = lean_box(0);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3356_);
lean_ctor_set(v___x_3358_, 1, v_fst_3344_);
v___x_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0___boxed(lean_object* v_fst_3361_, lean_object* v_fst_3362_, lean_object* v_specThm_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3361_, v_fst_3362_, v_specThm_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(lean_object* v_constName_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v_env_3385_; uint8_t v___x_3386_; lean_object* v___x_3387_; 
v___x_3384_ = lean_st_ref_get(v___y_3382_);
v_env_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc_ref(v_env_3385_);
lean_dec(v___x_3384_);
v___x_3386_ = 0;
lean_inc(v_constName_3374_);
v___x_3387_ = l_Lean_Environment_find_x3f(v_env_3385_, v_constName_3374_, v___x_3386_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
return v___x_3388_;
}
else
{
lean_object* v_val_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_constName_3374_);
v_val_3389_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3387_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_val_3389_);
lean_dec(v___x_3387_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 0);
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_val_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2___boxed(lean_object* v_constName_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_constName_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3407_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__7));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(lean_object* v_as_3431_, size_t v_sz_3432_, size_t v_i_3433_, lean_object* v_b_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_a_3445_; uint8_t v_starArg_3449_; 
v_starArg_3449_ = lean_usize_dec_lt(v_i_3433_, v_sz_3432_);
if (v_starArg_3449_ == 0)
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_b_3434_);
return v___x_3450_;
}
else
{
lean_object* v_snd_3451_; lean_object* v_fst_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3769_; 
v_snd_3451_ = lean_ctor_get(v_b_3434_, 1);
v_fst_3452_ = lean_ctor_get(v_b_3434_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_b_3434_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3454_ = v_b_3434_;
v_isShared_3455_ = v_isSharedCheck_3769_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snd_3451_);
lean_inc(v_fst_3452_);
lean_dec(v_b_3434_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3769_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v_fst_3456_; lean_object* v_snd_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3768_; 
v_fst_3456_ = lean_ctor_get(v_snd_3451_, 0);
v_snd_3457_ = lean_ctor_get(v_snd_3451_, 1);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_snd_3451_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3459_ = v_snd_3451_;
v_isShared_3460_ = v_isSharedCheck_3768_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_snd_3457_);
lean_inc(v_fst_3456_);
lean_dec(v_snd_3451_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3768_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_fst_3462_; lean_object* v_snd_3463_; lean_object* v_fst_3471_; lean_object* v_snd_3472_; lean_object* v_fst_3476_; lean_object* v_snd_3477_; lean_object* v___x_3480_; lean_object* v_a_3481_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3480_ = lean_unsigned_to_nat(1u);
v_a_3481_ = lean_array_uget_borrowed(v_as_3431_, v_i_3433_);
lean_inc(v_a_3481_);
v___x_3486_ = l_Lean_Syntax_getKind(v_a_3481_);
v___x_3487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2));
v___x_3488_ = lean_name_eq(v___x_3486_, v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; uint8_t v___x_3490_; 
v___x_3489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4));
v___x_3490_ = lean_name_eq(v___x_3486_, v___x_3489_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; uint8_t v___x_3492_; 
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
v___x_3491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6));
v___x_3492_ = lean_name_eq(v___x_3486_, v___x_3491_);
lean_dec(v___x_3486_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_dec_ref_known(v___x_3493_, 1);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v_fst_3456_);
lean_ctor_set(v___x_3494_, 1, v_snd_3457_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v_fst_3452_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v_a_3445_ = v___x_3495_;
goto v___jp_3444_;
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3496_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3493_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3493_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_dec(v_snd_3457_);
lean_inc(v_a_3481_);
v___x_3504_ = lean_array_push(v_fst_3456_, v_a_3481_);
v___x_3505_ = lean_box(v_starArg_3449_);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v_fst_3452_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v_a_3445_ = v___x_3507_;
goto v___jp_3444_;
}
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
lean_dec(v___x_3486_);
v___x_3508_ = lean_unsigned_to_nat(0u);
v___x_3509_ = l_Lean_Syntax_getArg(v_a_3481_, v___x_3508_);
v___x_3510_ = l_Lean_Syntax_isNone(v___x_3509_);
lean_dec(v___x_3509_);
if (v___x_3510_ == 0)
{
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
goto v___jp_3482_;
}
else
{
lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3511_ = l_Lean_Syntax_getArg(v_a_3481_, v___x_3480_);
v___x_3512_ = l_Lean_Syntax_isNone(v___x_3511_);
lean_dec(v___x_3511_);
if (v___x_3512_ == 0)
{
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
goto v___jp_3482_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v_a_3545_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3513_ = lean_unsigned_to_nat(2u);
v___x_3514_ = l_Lean_Syntax_getArg(v_a_3481_, v___x_3513_);
v___x_3641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__9));
v___x_3642_ = l_Lean_Meta_saveState___redArg(v___y_3440_, v___y_3442_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3644_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3642_, 1);
lean_inc(v___x_3514_);
v___x_3644_ = l_Lean_Elab_Term_resolveId_x3f(v___x_3514_, v___x_3641_, v_starArg_3449_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; 
lean_dec(v_a_3643_);
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v_a_3545_ = v_a_3645_;
goto v___jp_3544_;
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3677_; 
v_a_3646_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3648_ = v___x_3644_;
v_isShared_3649_ = v_isSharedCheck_3677_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3644_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3677_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
uint8_t v___x_3650_; 
v___x_3650_ = l_Lean_Exception_isInterrupt(v_a_3646_);
if (v___x_3650_ == 0)
{
uint8_t v___x_3651_; 
lean_inc(v_a_3646_);
v___x_3651_ = l_Lean_Exception_isRuntime(v_a_3646_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; 
lean_del_object(v___x_3648_);
lean_dec(v_a_3646_);
v___x_3652_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3643_, v___y_3440_, v___y_3442_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v___x_3653_; 
lean_dec_ref_known(v___x_3652_, 1);
lean_inc(v___x_3514_);
v___x_3653_ = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(v___x_3514_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v_a_3545_ = v_a_3654_;
goto v___jp_3544_;
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v___x_3514_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
v_a_3655_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3653_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3653_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v___x_3514_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
v_a_3663_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3652_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3652_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v___x_3672_; 
lean_dec(v_a_3643_);
lean_dec(v___x_3514_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
if (v_isShared_3649_ == 0)
{
v___x_3672_ = v___x_3648_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3646_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
else
{
lean_object* v___x_3675_; 
lean_dec(v_a_3643_);
lean_dec(v___x_3514_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
if (v_isShared_3649_ == 0)
{
v___x_3675_ = v___x_3648_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3646_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___x_3514_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
v_a_3678_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3642_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3642_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
v___jp_3515_:
{
lean_object* v_toCold_3520_; lean_object* v_currRecDepth_3521_; lean_object* v_ref_3522_; uint16_t v_optionFlags_3523_; uint8_t v_suppressElabErrors_3524_; uint8_t v_isRecordingDeps_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_ref_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_toCold_3520_ = lean_ctor_get(v___y_3518_, 0);
v_currRecDepth_3521_ = lean_ctor_get(v___y_3518_, 1);
v_ref_3522_ = lean_ctor_get(v___y_3518_, 2);
v_optionFlags_3523_ = lean_ctor_get_uint16(v___y_3518_, sizeof(void*)*3);
v_suppressElabErrors_3524_ = lean_ctor_get_uint8(v___y_3518_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3525_ = lean_ctor_get_uint8(v___y_3518_, sizeof(void*)*3 + 3);
v___x_3526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8);
lean_inc(v___x_3514_);
v___x_3527_ = l_Lean_MessageData_ofSyntax(v___x_3514_);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3528_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v_ref_3531_ = l_Lean_replaceRef(v___x_3514_, v_ref_3522_);
lean_dec(v___x_3514_);
lean_inc(v_currRecDepth_3521_);
lean_inc_ref(v_toCold_3520_);
v___x_3532_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3532_, 0, v_toCold_3520_);
lean_ctor_set(v___x_3532_, 1, v_currRecDepth_3521_);
lean_ctor_set(v___x_3532_, 2, v_ref_3531_);
lean_ctor_set_uint16(v___x_3532_, sizeof(void*)*3, v_optionFlags_3523_);
lean_ctor_set_uint8(v___x_3532_, sizeof(void*)*3 + 2, v_suppressElabErrors_3524_);
lean_ctor_set_uint8(v___x_3532_, sizeof(void*)*3 + 3, v_isRecordingDeps_3525_);
v___x_3533_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v___x_3530_, v___y_3516_, v___y_3517_, v___x_3532_, v___y_3519_);
lean_dec_ref_known(v___x_3532_, 3);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec_ref_known(v___x_3533_, 1);
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v_fst_3456_);
lean_ctor_set(v___x_3534_, 1, v_snd_3457_);
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v_fst_3452_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v_a_3445_ = v___x_3535_;
goto v___jp_3444_;
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3536_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3533_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3533_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
v___jp_3544_:
{
if (lean_obj_tag(v_a_3545_) == 1)
{
lean_object* v_val_3546_; 
v_val_3546_ = lean_ctor_get(v_a_3545_, 0);
lean_inc(v_val_3546_);
lean_dec_ref_known(v_a_3545_, 1);
switch(lean_obj_tag(v_val_3546_))
{
case 4:
{
lean_object* v_declName_3547_; lean_object* v___x_3548_; 
lean_dec(v___x_3514_);
v_declName_3547_ = lean_ctor_get(v_val_3546_, 0);
lean_inc_n(v_declName_3547_, 2);
lean_dec_ref_known(v_val_3546_, 2);
v___x_3548_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_declName_3547_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref_known(v___x_3548_, 1);
v___x_3549_ = lean_unsigned_to_nat(1000u);
v___x_3550_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3436_, v___y_3438_, v___y_3440_, v___y_3442_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3552_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_3547_, v___x_3549_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; 
lean_dec(v_a_3551_);
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
v___x_3554_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_3452_, v_a_3553_);
v_fst_3462_ = v___x_3554_;
v_snd_3463_ = v_fst_3456_;
goto v___jp_3461_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3577_; 
v_a_3555_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3557_ = v___x_3552_;
v_isShared_3558_ = v_isSharedCheck_3577_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3552_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3577_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
uint8_t v___x_3559_; 
v___x_3559_ = l_Lean_Exception_isInterrupt(v_a_3555_);
if (v___x_3559_ == 0)
{
uint8_t v___x_3560_; 
lean_inc(v_a_3555_);
v___x_3560_ = l_Lean_Exception_isRuntime(v_a_3555_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_del_object(v___x_3557_);
lean_dec(v_a_3555_);
v___x_3561_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3551_, v___x_3560_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3562_; 
lean_dec_ref_known(v___x_3561_, 1);
lean_inc(v_a_3481_);
v___x_3562_ = lean_array_push(v_fst_3456_, v_a_3481_);
v_fst_3462_ = v_fst_3452_;
v_snd_3463_ = v___x_3562_;
goto v___jp_3461_;
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
v_a_3563_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3561_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3561_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v___x_3572_; 
lean_dec(v_a_3551_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
if (v_isShared_3558_ == 0)
{
v___x_3572_ = v___x_3557_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3555_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
lean_object* v___x_3575_; 
lean_dec(v_a_3551_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
if (v_isShared_3558_ == 0)
{
v___x_3575_ = v___x_3557_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3555_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_declName_3547_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
v_a_3578_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3550_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3550_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_declName_3547_);
lean_del_object(v___x_3459_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_del_object(v___x_3454_);
lean_dec(v_fst_3452_);
v_a_3586_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3548_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3548_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3594_; lean_object* v___x_3595_; 
lean_dec(v___x_3514_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
v_fvarId_3594_ = lean_ctor_get(v_val_3546_, 0);
lean_inc(v_fvarId_3594_);
v___x_3595_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_val_3546_, v___y_3439_, v___y_3441_, v___y_3442_);
lean_dec_ref_known(v_val_3546_, 1);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_dec_ref_known(v___x_3595_, 1);
v___x_3596_ = lean_unsigned_to_nat(1000u);
v___x_3597_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3436_, v___y_3438_, v___y_3440_, v___y_3442_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvarId_3594_, v___x_3596_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; 
lean_dec(v_a_3598_);
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_3452_, v_a_3600_);
v_fst_3471_ = v___x_3601_;
v_snd_3472_ = v_fst_3456_;
goto v___jp_3470_;
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3624_; 
v_a_3602_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3604_ = v___x_3599_;
v_isShared_3605_ = v_isSharedCheck_3624_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3599_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3624_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
uint8_t v___x_3606_; 
v___x_3606_ = l_Lean_Exception_isInterrupt(v_a_3602_);
if (v___x_3606_ == 0)
{
uint8_t v___x_3607_; 
lean_inc(v_a_3602_);
v___x_3607_ = l_Lean_Exception_isRuntime(v_a_3602_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; 
lean_del_object(v___x_3604_);
lean_dec(v_a_3602_);
v___x_3608_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3598_, v___x_3607_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v___x_3609_; 
lean_dec_ref_known(v___x_3608_, 1);
lean_inc(v_a_3481_);
v___x_3609_ = lean_array_push(v_fst_3456_, v_a_3481_);
v_fst_3471_ = v_fst_3452_;
v_snd_3472_ = v___x_3609_;
goto v___jp_3470_;
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3610_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3608_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3608_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v___x_3619_; 
lean_dec(v_a_3598_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
if (v_isShared_3605_ == 0)
{
v___x_3619_ = v___x_3604_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3602_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
else
{
lean_object* v___x_3622_; 
lean_dec(v_a_3598_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
if (v_isShared_3605_ == 0)
{
v___x_3622_ = v___x_3604_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3602_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v_fvarId_3594_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3625_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3597_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3597_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_fvarId_3594_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3633_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3595_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3595_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
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
default: 
{
lean_dec(v_val_3546_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
v___y_3516_ = v___y_3439_;
v___y_3517_ = v___y_3440_;
v___y_3518_ = v___y_3441_;
v___y_3519_ = v___y_3442_;
goto v___jp_3515_;
}
}
}
else
{
lean_dec(v_a_3545_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
v___y_3516_ = v___y_3439_;
v___y_3517_ = v___y_3440_;
v___y_3518_ = v___y_3441_;
v___y_3519_ = v___y_3442_;
goto v___jp_3515_;
}
}
}
}
}
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_dec(v___x_3486_);
lean_del_object(v___x_3459_);
lean_del_object(v___x_3454_);
v___x_3686_ = l_Lean_Syntax_getArg(v_a_3481_, v___x_3480_);
v___x_3687_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3436_, v___y_3438_, v___y_3440_, v___y_3442_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3759_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3690_ = v___x_3687_;
v_isShared_3691_ = v_isSharedCheck_3759_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3687_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3759_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v_a_3693_; lean_object* v___y_3713_; lean_object* v___x_3719_; 
lean_inc(v___x_3686_);
v___x_3719_ = l_Lean_Elab_Term_isLocalIdent_x3f(v___x_3686_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3719_, 1);
if (lean_obj_tag(v_a_3720_) == 1)
{
lean_object* v_val_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec(v___x_3686_);
v_val_3721_ = lean_ctor_get(v_a_3720_, 0);
lean_inc(v_val_3721_);
lean_dec_ref_known(v_a_3720_, 1);
v___x_3722_ = l_Lean_Expr_fvarId_x21(v_val_3721_);
lean_dec(v_val_3721_);
v___x_3723_ = lean_unsigned_to_nat(1000u);
v___x_3724_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_3722_, v___x_3723_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
lean_inc(v_fst_3456_);
lean_inc(v_fst_3452_);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3452_, v_fst_3456_, v_a_3725_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
v___y_3713_ = v___x_3726_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3727_; 
v_a_3727_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3724_, 1);
v_a_3693_ = v_a_3727_;
goto v___jp_3692_;
}
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_dec(v_a_3720_);
v___x_3728_ = lean_box(0);
v___x_3729_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3436_, v___y_3438_, v___y_3440_, v___y_3442_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
lean_inc(v___x_3686_);
v___x_3731_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_3686_, v___x_3728_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec(v_a_3730_);
lean_dec(v___x_3686_);
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v___x_3733_ = lean_unsigned_to_nat(1000u);
v___x_3734_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_a_3732_, v___x_3733_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3736_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3734_, 1);
lean_inc(v_fst_3456_);
lean_inc(v_fst_3452_);
v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3452_, v_fst_3456_, v_a_3735_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
v___y_3713_ = v___x_3736_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3737_; 
v_a_3737_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3734_, 1);
v_a_3693_ = v_a_3737_;
goto v___jp_3692_;
}
}
else
{
lean_object* v_a_3738_; uint8_t v___x_3739_; 
v_a_3738_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3731_, 1);
v___x_3739_ = l_Lean_Exception_isInterrupt(v_a_3738_);
if (v___x_3739_ == 0)
{
uint8_t v___x_3740_; 
lean_inc(v_a_3738_);
v___x_3740_ = l_Lean_Exception_isRuntime(v_a_3738_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec(v_a_3738_);
v___x_3741_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3730_, v___x_3740_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_toCold_3742_; lean_object* v_currRecDepth_3743_; lean_object* v_ref_3744_; uint16_t v_optionFlags_3745_; uint8_t v_suppressElabErrors_3746_; uint8_t v_isRecordingDeps_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v_ref_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_dec_ref_known(v___x_3741_, 1);
v_toCold_3742_ = lean_ctor_get(v___y_3441_, 0);
v_currRecDepth_3743_ = lean_ctor_get(v___y_3441_, 1);
v_ref_3744_ = lean_ctor_get(v___y_3441_, 2);
v_optionFlags_3745_ = lean_ctor_get_uint16(v___y_3441_, sizeof(void*)*3);
v_suppressElabErrors_3746_ = lean_ctor_get_uint8(v___y_3441_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3747_ = lean_ctor_get_uint8(v___y_3441_, sizeof(void*)*3 + 3);
v___x_3748_ = l_Lean_Syntax_getId(v___x_3686_);
v___x_3749_ = l_Lean_Name_eraseMacroScopes(v___x_3748_);
lean_dec(v___x_3748_);
v_ref_3750_ = l_Lean_replaceRef(v___x_3686_, v_ref_3744_);
lean_dec(v___x_3686_);
lean_inc(v_currRecDepth_3743_);
lean_inc_ref(v_toCold_3742_);
v___x_3751_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3751_, 0, v_toCold_3742_);
lean_ctor_set(v___x_3751_, 1, v_currRecDepth_3743_);
lean_ctor_set(v___x_3751_, 2, v_ref_3750_);
lean_ctor_set_uint16(v___x_3751_, sizeof(void*)*3, v_optionFlags_3745_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*3 + 2, v_suppressElabErrors_3746_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*3 + 3, v_isRecordingDeps_3747_);
v___x_3752_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v___x_3749_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___x_3751_, v___y_3442_);
lean_dec_ref_known(v___x_3751_, 3);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3754_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3752_, 1);
lean_inc(v_fst_3456_);
lean_inc(v_fst_3452_);
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3452_, v_fst_3456_, v_a_3753_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
v___y_3713_ = v___x_3754_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3752_, 1);
v_a_3693_ = v_a_3755_;
goto v___jp_3692_;
}
}
else
{
lean_object* v_a_3756_; 
lean_dec(v___x_3686_);
v_a_3756_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3741_, 1);
v_a_3693_ = v_a_3756_;
goto v___jp_3692_;
}
}
else
{
lean_dec(v_a_3730_);
lean_dec(v___x_3686_);
v_a_3693_ = v_a_3738_;
goto v___jp_3692_;
}
}
else
{
lean_dec(v_a_3730_);
lean_dec(v___x_3686_);
v_a_3693_ = v_a_3738_;
goto v___jp_3692_;
}
}
}
else
{
lean_object* v_a_3757_; 
lean_dec(v___x_3686_);
v_a_3757_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3729_, 1);
v_a_3693_ = v_a_3757_;
goto v___jp_3692_;
}
}
}
else
{
lean_object* v_a_3758_; 
lean_dec(v___x_3686_);
v_a_3758_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3719_, 1);
v_a_3693_ = v_a_3758_;
goto v___jp_3692_;
}
v___jp_3692_:
{
uint8_t v___x_3694_; 
v___x_3694_ = l_Lean_Exception_isInterrupt(v_a_3693_);
if (v___x_3694_ == 0)
{
uint8_t v___x_3695_; 
lean_inc_ref(v_a_3693_);
v___x_3695_ = l_Lean_Exception_isRuntime(v_a_3693_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; 
lean_dec_ref(v_a_3693_);
lean_del_object(v___x_3690_);
v___x_3696_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3688_, v___x_3695_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v___x_3697_; 
lean_dec_ref_known(v___x_3696_, 1);
lean_inc(v_a_3481_);
v___x_3697_ = lean_array_push(v_fst_3456_, v_a_3481_);
v_fst_3476_ = v_fst_3452_;
v_snd_3477_ = v___x_3697_;
goto v___jp_3475_;
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3698_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3696_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3696_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v___x_3707_; 
lean_dec(v_a_3688_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set_tag(v___x_3690_, 1);
lean_ctor_set(v___x_3690_, 0, v_a_3693_);
v___x_3707_ = v___x_3690_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3693_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v___x_3710_; 
lean_dec(v_a_3688_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set_tag(v___x_3690_, 1);
lean_ctor_set(v___x_3690_, 0, v_a_3693_);
v___x_3710_ = v___x_3690_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3693_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
v___jp_3712_:
{
if (lean_obj_tag(v___y_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v_snd_3715_; lean_object* v_fst_3716_; lean_object* v_snd_3717_; 
lean_del_object(v___x_3690_);
lean_dec(v_a_3688_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3714_ = lean_ctor_get(v___y_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___y_3713_, 1);
v_snd_3715_ = lean_ctor_get(v_a_3714_, 1);
lean_inc(v_snd_3715_);
lean_dec(v_a_3714_);
v_fst_3716_ = lean_ctor_get(v_snd_3715_, 0);
lean_inc(v_fst_3716_);
v_snd_3717_ = lean_ctor_get(v_snd_3715_, 1);
lean_inc(v_snd_3717_);
lean_dec(v_snd_3715_);
v_fst_3476_ = v_fst_3716_;
v_snd_3477_ = v_snd_3717_;
goto v___jp_3475_;
}
else
{
lean_object* v_a_3718_; 
v_a_3718_ = lean_ctor_get(v___y_3713_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___y_3713_, 1);
v_a_3693_ = v_a_3718_;
goto v___jp_3692_;
}
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec(v___x_3686_);
lean_dec(v_snd_3457_);
lean_dec(v_fst_3456_);
lean_dec(v_fst_3452_);
v_a_3760_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3687_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3687_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
v___jp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v_snd_3463_);
v___x_3465_ = v___x_3459_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_snd_3463_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_snd_3457_);
v___x_3465_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v___x_3465_);
lean_ctor_set(v___x_3454_, 0, v_fst_3462_);
v___x_3467_ = v___x_3454_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_fst_3462_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
v_a_3445_ = v___x_3467_;
goto v___jp_3444_;
}
}
}
v___jp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v_snd_3472_);
lean_ctor_set(v___x_3473_, 1, v_snd_3457_);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v_fst_3471_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v_a_3445_ = v___x_3474_;
goto v___jp_3444_;
}
v___jp_3475_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_snd_3477_);
lean_ctor_set(v___x_3478_, 1, v_snd_3457_);
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v_fst_3476_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v_a_3445_ = v___x_3479_;
goto v___jp_3444_;
}
v___jp_3482_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_inc(v_a_3481_);
v___x_3483_ = lean_array_push(v_fst_3456_, v_a_3481_);
v___x_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v_snd_3457_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_fst_3452_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v_a_3445_ = v___x_3485_;
goto v___jp_3444_;
}
}
}
}
v___jp_3444_:
{
size_t v___x_3446_; size_t v___x_3447_; 
v___x_3446_ = ((size_t)1ULL);
v___x_3447_ = lean_usize_add(v_i_3433_, v___x_3446_);
v_i_3433_ = v___x_3447_;
v_b_3434_ = v_a_3445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___boxed(lean_object* v_as_3770_, lean_object* v_sz_3771_, lean_object* v_i_3772_, lean_object* v_b_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
size_t v_sz_boxed_3783_; size_t v_i_boxed_3784_; lean_object* v_res_3785_; 
v_sz_boxed_3783_ = lean_unbox_usize(v_sz_3771_);
lean_dec(v_sz_3771_);
v_i_boxed_3784_ = lean_unbox_usize(v_i_3772_);
lean_dec(v_i_3772_);
v_res_3785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v_as_3770_, v_sz_boxed_3783_, v_i_boxed_3784_, v_b_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v_as_3770_);
return v_res_3785_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15(void){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14));
v___x_3826_ = l_String_toRawSubstring_x27(v___x_3825_);
return v___x_3826_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20));
v___x_3838_ = l_String_toRawSubstring_x27(v___x_3837_);
return v___x_3838_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23(void){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Array_mkArray0___redArg();
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext(lean_object* v_optConfig_3846_, lean_object* v_lemmas_3847_, uint8_t v_ignoreStarArg_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
uint8_t v_starArg_3858_; uint8_t v_starArg_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v_starArg_3858_ = 1;
v_starArg_3859_ = 0;
v___x_3860_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0));
v___x_3861_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_optConfig_3846_, v___x_3860_, v_starArg_3858_, v_a_3849_, v_a_3855_, v_a_3856_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3863_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3861_, 1);
v___x_3863_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3856_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; size_t v_sz_3870_; size_t v___x_3871_; lean_object* v___x_3872_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v___x_3865_ = lean_unsigned_to_nat(1u);
v___x_3866_ = l_Lean_Syntax_getArg(v_lemmas_3847_, v___x_3865_);
v___x_3867_ = l_Lean_Syntax_getSepArgs(v___x_3866_);
lean_dec(v___x_3866_);
v___x_3868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2));
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v_a_3864_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v_sz_3870_ = lean_array_size(v___x_3867_);
v___x_3871_ = ((size_t)0ULL);
v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v___x_3867_, v_sz_3870_, v___x_3871_, v___x_3869_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
lean_dec_ref(v___x_3867_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; lean_object* v_snd_3874_; lean_object* v_toCold_3875_; lean_object* v_fst_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3983_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
v_snd_3874_ = lean_ctor_get(v_a_3873_, 1);
lean_inc(v_snd_3874_);
v_toCold_3875_ = lean_ctor_get(v_a_3855_, 0);
v_fst_3876_ = lean_ctor_get(v_a_3873_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_a_3873_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; 
v_unused_3984_ = lean_ctor_get(v_a_3873_, 1);
lean_dec(v_unused_3984_);
v___x_3878_ = v_a_3873_;
v_isShared_3879_ = v_isSharedCheck_3983_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_fst_3876_);
lean_dec(v_a_3873_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3983_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v_fst_3880_; lean_object* v_snd_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3982_; 
v_fst_3880_ = lean_ctor_get(v_snd_3874_, 0);
v_snd_3881_ = lean_ctor_get(v_snd_3874_, 1);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_snd_3874_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3883_ = v_snd_3874_;
v_isShared_3884_ = v_isSharedCheck_3982_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_snd_3881_);
lean_inc(v_fst_3880_);
lean_dec(v_snd_3874_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3982_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v_ref_3885_; lean_object* v_quotContext_3886_; lean_object* v_currMacroScope_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
v_ref_3885_ = lean_ctor_get(v_a_3855_, 2);
v_quotContext_3886_ = lean_ctor_get(v_toCold_3875_, 8);
v_currMacroScope_3887_ = lean_ctor_get(v_toCold_3875_, 9);
v___x_3888_ = l_Lean_SourceInfo_fromRef(v_ref_3885_, v_starArg_3859_);
v___x_3889_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3));
v___x_3890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4));
lean_inc(v___x_3888_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set_tag(v___x_3883_, 2);
lean_ctor_set(v___x_3883_, 1, v___x_3889_);
lean_ctor_set(v___x_3883_, 0, v___x_3888_);
v___x_3892_ = v___x_3883_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___x_3889_);
v___x_3892_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3899_; 
v___x_3893_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6));
v___x_3894_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8));
v___x_3895_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10));
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12));
v___x_3897_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13));
lean_inc(v___x_3888_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set_tag(v___x_3878_, 2);
lean_ctor_set(v___x_3878_, 1, v___x_3897_);
lean_ctor_set(v___x_3878_, 0, v___x_3888_);
v___x_3899_ = v___x_3878_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v___x_3897_);
v___x_3899_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3900_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15);
v___x_3901_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16));
lean_inc_n(v_currMacroScope_3887_, 2);
lean_inc_n(v_quotContext_3886_, 2);
v___x_3902_ = l_Lean_addMacroScope(v_quotContext_3886_, v___x_3901_, v_currMacroScope_3887_);
v___x_3903_ = lean_box(0);
lean_inc_n(v___x_3888_, 14);
v___x_3904_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3888_);
lean_ctor_set(v___x_3904_, 1, v___x_3900_);
lean_ctor_set(v___x_3904_, 2, v___x_3902_);
lean_ctor_set(v___x_3904_, 3, v___x_3903_);
v___x_3905_ = l_Lean_Syntax_node2(v___x_3888_, v___x_3896_, v___x_3899_, v___x_3904_);
v___x_3906_ = l_Lean_Syntax_node1(v___x_3888_, v___x_3895_, v___x_3905_);
v___x_3907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18));
v___x_3908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19));
v___x_3909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3888_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21);
v___x_3911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22));
v___x_3912_ = l_Lean_addMacroScope(v_quotContext_3886_, v___x_3911_, v_currMacroScope_3887_);
v___x_3913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3888_);
lean_ctor_set(v___x_3913_, 1, v___x_3910_);
lean_ctor_set(v___x_3913_, 2, v___x_3912_);
lean_ctor_set(v___x_3913_, 3, v___x_3903_);
v___x_3914_ = l_Lean_Syntax_node2(v___x_3888_, v___x_3907_, v___x_3909_, v___x_3913_);
v___x_3915_ = l_Lean_Syntax_node1(v___x_3888_, v___x_3895_, v___x_3914_);
v___x_3916_ = l_Lean_Syntax_node2(v___x_3888_, v___x_3894_, v___x_3906_, v___x_3915_);
v___x_3917_ = l_Lean_Syntax_node1(v___x_3888_, v___x_3893_, v___x_3916_);
v___x_3918_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23);
v___x_3919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3888_);
lean_ctor_set(v___x_3919_, 1, v___x_3894_);
lean_ctor_set(v___x_3919_, 2, v___x_3918_);
v___x_3920_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24));
v___x_3921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3888_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25));
v___x_3923_ = l_Lean_Syntax_SepArray_ofElems(v___x_3922_, v_fst_3880_);
lean_dec(v_fst_3880_);
v___x_3924_ = l_Array_append___redArg(v___x_3918_, v___x_3923_);
lean_dec_ref(v___x_3923_);
v___x_3925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3888_);
lean_ctor_set(v___x_3925_, 1, v___x_3894_);
lean_ctor_set(v___x_3925_, 2, v___x_3924_);
v___x_3926_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26));
v___x_3927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3888_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = l_Lean_Syntax_node3(v___x_3888_, v___x_3894_, v___x_3921_, v___x_3925_, v___x_3927_);
lean_inc_ref_n(v___x_3919_, 2);
v___x_3929_ = l_Lean_Syntax_node6(v___x_3888_, v___x_3890_, v___x_3892_, v___x_3917_, v___x_3919_, v___x_3919_, v___x_3928_, v___x_3919_);
v___x_3930_ = 0;
v___x_3931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__27));
v___x_3932_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_3929_, v_starArg_3859_, v___x_3930_, v_ignoreStarArg_3848_, v___x_3931_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
lean_dec(v___x_3929_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3971_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3935_ = v___x_3932_;
v_isShared_3936_ = v_isSharedCheck_3971_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3932_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3971_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v_specThms_3938_; lean_object* v___y_3939_; uint8_t v___x_3949_; 
v___x_3949_ = lean_unbox(v_snd_3881_);
lean_dec(v_snd_3881_);
if (v___x_3949_ == 0)
{
v_specThms_3938_ = v_fst_3876_;
v___y_3939_ = v_a_3853_;
goto v___jp_3937_;
}
else
{
if (v_ignoreStarArg_3848_ == 0)
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Meta_getPropHyps(v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; size_t v_sz_3952_; lean_object* v___x_3953_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
v_sz_3952_ = lean_array_size(v_a_3951_);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_a_3951_, v_sz_3952_, v___x_3871_, v_fst_3876_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
lean_dec(v_a_3951_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v_specThms_3938_ = v_a_3954_;
v___y_3939_ = v_a_3853_;
goto v___jp_3937_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_del_object(v___x_3935_);
lean_dec(v_a_3933_);
lean_dec(v_a_3862_);
v_a_3955_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3953_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3953_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_del_object(v___x_3935_);
lean_dec(v_a_3933_);
lean_dec(v_fst_3876_);
lean_dec(v_a_3862_);
v_a_3963_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3950_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3950_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
v_specThms_3938_ = v_fst_3876_;
v___y_3939_ = v_a_3853_;
goto v___jp_3937_;
}
}
v___jp_3937_:
{
lean_object* v_lctx_3940_; lean_object* v_ctx_3941_; lean_object* v_simprocs_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
v_lctx_3940_ = lean_ctor_get(v___y_3939_, 2);
v_ctx_3941_ = lean_ctor_get(v_a_3933_, 0);
lean_inc_ref(v_ctx_3941_);
v_simprocs_3942_ = lean_ctor_get(v_a_3933_, 1);
lean_inc_ref(v_simprocs_3942_);
lean_dec(v_a_3933_);
v___x_3943_ = lean_box(1);
lean_inc_ref(v_lctx_3940_);
v___x_3944_ = lean_local_ctx_num_indices(v_lctx_3940_);
v___x_3945_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3945_, 0, v_a_3862_);
lean_ctor_set(v___x_3945_, 1, v_specThms_3938_);
lean_ctor_set(v___x_3945_, 2, v_ctx_3941_);
lean_ctor_set(v___x_3945_, 3, v_simprocs_3942_);
lean_ctor_set(v___x_3945_, 4, v___x_3943_);
lean_ctor_set(v___x_3945_, 5, v___x_3944_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 0, v___x_3945_);
v___x_3947_ = v___x_3935_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_snd_3881_);
lean_dec(v_fst_3876_);
lean_dec(v_a_3862_);
v_a_3972_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3932_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3932_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
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
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_dec(v_a_3862_);
v_a_3985_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3872_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3872_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec(v_a_3862_);
v_a_3993_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3863_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3863_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4001_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3861_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3861_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___boxed(lean_object* v_optConfig_4009_, lean_object* v_lemmas_4010_, lean_object* v_ignoreStarArg_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
uint8_t v_ignoreStarArg_boxed_4021_; lean_object* v_res_4022_; 
v_ignoreStarArg_boxed_4021_ = lean_unbox(v_ignoreStarArg_4011_);
v_res_4022_ = l_Lean_Elab_Tactic_Do_mkSpecContext(v_optConfig_4009_, v_lemmas_4010_, v_ignoreStarArg_boxed_4021_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
lean_dec(v_lemmas_4010_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(lean_object* v_00_u03b1_4023_, lean_object* v_msg_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_4024_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___boxed(lean_object* v_00_u03b1_4035_, lean_object* v_msg_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(v_00_u03b1_4035_, v_msg_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(lean_object* v_00_u03b1_4047_, lean_object* v_constName_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___boxed(lean_object* v_00_u03b1_4059_, lean_object* v_constName_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(v_00_u03b1_4059_, v_constName_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(lean_object* v_as_4071_, size_t v_sz_4072_, size_t v_i_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_4071_, v_sz_4072_, v_i_4073_, v_b_4074_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___boxed(lean_object* v_as_4085_, lean_object* v_sz_4086_, lean_object* v_i_4087_, lean_object* v_b_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
size_t v_sz_boxed_4098_; size_t v_i_boxed_4099_; lean_object* v_res_4100_; 
v_sz_boxed_4098_ = lean_unbox_usize(v_sz_4086_);
lean_dec(v_sz_4086_);
v_i_boxed_4099_ = lean_unbox_usize(v_i_4087_);
lean_dec(v_i_4087_);
v_res_4100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(v_as_4085_, v_sz_boxed_4098_, v_i_boxed_4099_, v_b_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec_ref(v_as_4085_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(lean_object* v_00_u03b1_4101_, lean_object* v_ref_4102_, lean_object* v_constName_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_4102_, v_constName_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___boxed(lean_object* v_00_u03b1_4114_, lean_object* v_ref_4115_, lean_object* v_constName_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(v_00_u03b1_4114_, v_ref_4115_, v_constName_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v_ref_4115_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_4127_, lean_object* v_ref_4128_, lean_object* v_msg_4129_, lean_object* v_declHint_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_4128_, v_msg_4129_, v_declHint_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4141_, lean_object* v_ref_4142_, lean_object* v_msg_4143_, lean_object* v_declHint_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(v_00_u03b1_4141_, v_ref_4142_, v_msg_4143_, v_declHint_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v_ref_4142_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_4155_, lean_object* v_declHint_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_4155_, v_declHint_4156_, v___y_4164_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_4167_, lean_object* v_declHint_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_4167_, v_declHint_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(lean_object* v_00_u03b1_4179_, lean_object* v_ref_4180_, lean_object* v_msg_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_4180_, v_msg_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b1_4192_, lean_object* v_ref_4193_, lean_object* v_msg_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(v_00_u03b1_4192_, v_ref_4193_, v_msg_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v_ref_4193_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_toCold_4213_; lean_object* v_options_4214_; lean_object* v___x_4215_; 
v_toCold_4213_ = lean_ctor_get(v___y_4210_, 0);
v_options_4214_ = lean_ctor_get(v_toCold_4213_, 2);
lean_inc_ref(v_options_4214_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_options_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed(lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v_toCold_4233_; lean_object* v_inheritedTraceOptions_4234_; lean_object* v___x_4235_; 
v_toCold_4233_ = lean_ctor_get(v___y_4230_, 0);
v_inheritedTraceOptions_4234_ = lean_ctor_get(v_toCold_4233_, 11);
lean_inc_ref(v_inheritedTraceOptions_4234_);
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v_inheritedTraceOptions_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed(lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(lean_object* v___x_4245_, lean_object* v___x_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_4245_, v___x_4246_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed(lean_object* v___x_4256_, lean_object* v___x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(v___x_4256_, v___x_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
return v_res_4266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4(void){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4269_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_4272_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4271_, v___x_4270_, v___x_4269_);
return v___x_4272_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___f_4276_; lean_object* v___f_4277_; lean_object* v___x_4278_; 
v___x_4275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4);
v___f_4276_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_4278_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4277_, v___f_4276_, v___x_4275_);
return v___x_4278_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6(void){
_start:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5);
v___x_4280_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4281_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_4282_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4281_, v___x_4280_, v___x_4279_);
return v___x_4282_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7(void){
_start:
{
lean_object* v___x_4283_; lean_object* v___f_4284_; lean_object* v___f_4285_; lean_object* v___x_4286_; 
v___x_4283_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6);
v___f_4284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_4286_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4285_, v___f_4284_, v___x_4283_);
return v___x_4286_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8(void){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_instMonadEIO___redArg();
return v___x_4287_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9(void){
_start:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4288_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8);
v___x_4289_ = l_StateRefT_x27_instMonad___redArg(v___x_4288_);
return v___x_4289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = l_Lean_Core_instMonadTraceCoreM;
v___x_4295_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4296_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_4295_, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___f_4298_; lean_object* v___x_4299_; 
v___x_4297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14);
v___f_4298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4299_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4298_, v___x_4297_);
return v___x_4299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16(void){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15);
v___x_4301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4302_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_4301_, v___x_4300_);
return v___x_4302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17(void){
_start:
{
lean_object* v___x_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; 
v___x_4303_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16);
v___f_4304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4305_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4304_, v___x_4303_);
return v___x_4305_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18(void){
_start:
{
lean_object* v___x_4306_; lean_object* v___f_4307_; lean_object* v___x_4308_; 
v___x_4306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17);
v___f_4307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4308_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4307_, v___x_4306_);
return v___x_4308_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19(void){
_start:
{
lean_object* v___x_4309_; lean_object* v___f_4310_; lean_object* v___x_4311_; 
v___x_4309_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18);
v___f_4310_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___x_4311_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4310_, v___x_4309_);
return v___x_4311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22(void){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; 
v___x_4314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4315_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4316_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4316_, 0, v___x_4315_);
lean_closure_set(v___f_4316_, 1, v___x_4314_);
return v___f_4316_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23(void){
_start:
{
lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___f_4319_; 
v___f_4317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4318_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22);
v___f_4319_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4319_, 0, v___f_4318_);
lean_closure_set(v___f_4319_, 1, v___f_4317_);
return v___f_4319_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24(void){
_start:
{
lean_object* v___f_4320_; lean_object* v___f_4321_; lean_object* v___f_4322_; 
v___f_4320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4321_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23);
v___f_4322_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4322_, 0, v___f_4321_);
lean_closure_set(v___f_4322_, 1, v___f_4320_);
return v___f_4322_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25(void){
_start:
{
lean_object* v___f_4323_; lean_object* v___f_4324_; lean_object* v___f_4325_; 
v___f_4323_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___f_4324_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24);
v___f_4325_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4325_, 0, v___f_4324_);
lean_closure_set(v___f_4325_, 1, v___f_4323_);
return v___f_4325_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28(void){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_4330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27));
v___x_4331_ = l_Lean_Name_append(v___x_4330_, v___x_4329_);
return v___x_4331_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29));
v___x_4334_ = l_Lean_stringToMessageData(v___x_4333_);
return v___x_4334_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31));
v___x_4337_ = l_Lean_stringToMessageData(v___x_4336_);
return v___x_4337_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33));
v___x_4340_ = l_Lean_stringToMessageData(v___x_4339_);
return v___x_4340_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36(void){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__35));
v___x_4343_ = l_Lean_stringToMessageData(v___x_4342_);
return v___x_4343_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38(void){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__37));
v___x_4346_ = l_Lean_stringToMessageData(v___x_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(lean_object* v_xs_4347_, lean_object* v_k_4348_, lean_object* v_runInBase_4349_, lean_object* v_i_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_){
_start:
{
lean_object* v___y_4359_; lean_object* v_a_4360_; lean_object* v_a_4367_; lean_object* v___y_4370_; lean_object* v___x_4372_; lean_object* v_toMonadRef_4373_; lean_object* v___x_4374_; lean_object* v_toApplicative_4375_; lean_object* v_toFunctor_4376_; lean_object* v_toSeq_4377_; lean_object* v_toSeqLeft_4378_; lean_object* v_toSeqRight_4379_; lean_object* v___f_4380_; lean_object* v___f_4381_; lean_object* v___f_4382_; lean_object* v___f_4383_; lean_object* v___x_4384_; lean_object* v___f_4385_; lean_object* v___f_4386_; lean_object* v___f_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v_toApplicative_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4489_; 
v___x_4372_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7);
v_toMonadRef_4373_ = lean_ctor_get(v___x_4372_, 0);
v___x_4374_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9);
v_toApplicative_4375_ = lean_ctor_get(v___x_4374_, 0);
v_toFunctor_4376_ = lean_ctor_get(v_toApplicative_4375_, 0);
v_toSeq_4377_ = lean_ctor_get(v_toApplicative_4375_, 2);
v_toSeqLeft_4378_ = lean_ctor_get(v_toApplicative_4375_, 3);
v_toSeqRight_4379_ = lean_ctor_get(v_toApplicative_4375_, 4);
v___f_4380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__10));
v___f_4381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__11));
lean_inc_ref_n(v_toFunctor_4376_, 2);
v___f_4382_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4382_, 0, v_toFunctor_4376_);
v___f_4383_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4383_, 0, v_toFunctor_4376_);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___f_4382_);
lean_ctor_set(v___x_4384_, 1, v___f_4383_);
lean_inc(v_toSeqRight_4379_);
v___f_4385_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4385_, 0, v_toSeqRight_4379_);
lean_inc(v_toSeqLeft_4378_);
v___f_4386_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4386_, 0, v_toSeqLeft_4378_);
lean_inc(v_toSeq_4377_);
v___f_4387_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4387_, 0, v_toSeq_4377_);
v___x_4388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4384_);
lean_ctor_set(v___x_4388_, 1, v___f_4380_);
lean_ctor_set(v___x_4388_, 2, v___f_4387_);
lean_ctor_set(v___x_4388_, 3, v___f_4386_);
lean_ctor_set(v___x_4388_, 4, v___f_4385_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
lean_ctor_set(v___x_4389_, 1, v___f_4381_);
v___x_4390_ = l_StateRefT_x27_instMonad___redArg(v___x_4389_);
v_toApplicative_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; 
v_unused_4490_ = lean_ctor_get(v___x_4390_, 1);
lean_dec(v_unused_4490_);
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4489_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_toApplicative_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4489_;
goto v_resetjp_4392_;
}
v___jp_4358_:
{
uint8_t v___x_4361_; 
v___x_4361_ = l_Lean_Exception_isInterrupt(v_a_4360_);
if (v___x_4361_ == 0)
{
uint8_t v___x_4362_; 
lean_inc_ref(v_a_4360_);
v___x_4362_ = l_Lean_Exception_isRuntime(v_a_4360_);
if (v___x_4362_ == 0)
{
if (lean_obj_tag(v_a_4360_) == 0)
{
lean_object* v___x_4363_; lean_object* v___x_4364_; 
lean_dec_ref_known(v_a_4360_, 2);
lean_dec_ref(v___y_4359_);
v___x_4363_ = lean_unsigned_to_nat(1u);
v___x_4364_ = lean_nat_add(v_i_4350_, v___x_4363_);
lean_dec(v_i_4350_);
v_i_4350_ = v___x_4364_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_4360_, 2);
lean_dec(v_i_4350_);
lean_dec_ref(v_runInBase_4349_);
lean_dec(v_k_4348_);
return v___y_4359_;
}
}
else
{
lean_dec_ref(v_a_4360_);
lean_dec(v_i_4350_);
lean_dec_ref(v_runInBase_4349_);
lean_dec(v_k_4348_);
return v___y_4359_;
}
}
else
{
lean_dec_ref(v_a_4360_);
lean_dec(v_i_4350_);
lean_dec_ref(v_runInBase_4349_);
lean_dec(v_k_4348_);
return v___y_4359_;
}
}
v___jp_4366_:
{
lean_object* v___x_4368_; 
lean_inc_ref(v_a_4367_);
v___x_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4368_, 0, v_a_4367_);
v___y_4359_ = v___x_4368_;
v_a_4360_ = v_a_4367_;
goto v___jp_4358_;
}
v___jp_4369_:
{
if (lean_obj_tag(v___y_4370_) == 0)
{
lean_dec(v_i_4350_);
lean_dec_ref(v_runInBase_4349_);
lean_dec(v_k_4348_);
return v___y_4370_;
}
else
{
lean_object* v_a_4371_; 
v_a_4371_ = lean_ctor_get(v___y_4370_, 0);
lean_inc(v_a_4371_);
v___y_4359_ = v___y_4370_;
v_a_4360_ = v_a_4371_;
goto v___jp_4358_;
}
}
v_resetjp_4392_:
{
lean_object* v_toFunctor_4395_; lean_object* v_toSeq_4396_; lean_object* v_toSeqLeft_4397_; lean_object* v_toSeqRight_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4487_; 
v_toFunctor_4395_ = lean_ctor_get(v_toApplicative_4391_, 0);
v_toSeq_4396_ = lean_ctor_get(v_toApplicative_4391_, 2);
v_toSeqLeft_4397_ = lean_ctor_get(v_toApplicative_4391_, 3);
v_toSeqRight_4398_ = lean_ctor_get(v_toApplicative_4391_, 4);
v_isSharedCheck_4487_ = !lean_is_exclusive(v_toApplicative_4391_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; 
v_unused_4488_ = lean_ctor_get(v_toApplicative_4391_, 1);
lean_dec(v_unused_4488_);
v___x_4400_ = v_toApplicative_4391_;
v_isShared_4401_ = v_isSharedCheck_4487_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_toSeqRight_4398_);
lean_inc(v_toSeqLeft_4397_);
lean_inc(v_toSeq_4396_);
lean_inc(v_toFunctor_4395_);
lean_dec(v_toApplicative_4391_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4487_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___f_4402_; lean_object* v___f_4403_; lean_object* v___f_4404_; lean_object* v___f_4405_; lean_object* v___x_4406_; lean_object* v___f_4407_; lean_object* v___f_4408_; lean_object* v___f_4409_; lean_object* v___x_4411_; 
v___f_4402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__12));
v___f_4403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__13));
lean_inc_ref(v_toFunctor_4395_);
v___f_4404_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4404_, 0, v_toFunctor_4395_);
v___f_4405_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4405_, 0, v_toFunctor_4395_);
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___f_4404_);
lean_ctor_set(v___x_4406_, 1, v___f_4405_);
v___f_4407_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4407_, 0, v_toSeqRight_4398_);
v___f_4408_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4408_, 0, v_toSeqLeft_4397_);
v___f_4409_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4409_, 0, v_toSeq_4396_);
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 4, v___f_4407_);
lean_ctor_set(v___x_4400_, 3, v___f_4408_);
lean_ctor_set(v___x_4400_, 2, v___f_4409_);
lean_ctor_set(v___x_4400_, 1, v___f_4402_);
lean_ctor_set(v___x_4400_, 0, v___x_4406_);
v___x_4411_ = v___x_4400_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4406_);
lean_ctor_set(v_reuseFailAlloc_4486_, 1, v___f_4402_);
lean_ctor_set(v_reuseFailAlloc_4486_, 2, v___f_4409_);
lean_ctor_set(v_reuseFailAlloc_4486_, 3, v___f_4408_);
lean_ctor_set(v_reuseFailAlloc_4486_, 4, v___f_4407_);
v___x_4411_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4413_; 
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 1, v___f_4403_);
lean_ctor_set(v___x_4393_, 0, v___x_4411_);
v___x_4413_ = v___x_4393_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4485_, 1, v___f_4403_);
v___x_4413_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; uint8_t v___x_4418_; 
v___x_4414_ = l_StateRefT_x27_instMonad___redArg(v___x_4413_);
v___x_4415_ = l_ReaderT_instMonad___redArg(v___x_4414_);
v___x_4416_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19);
v___x_4417_ = lean_array_get_size(v_xs_4347_);
v___x_4418_ = lean_nat_dec_lt(v_i_4350_, v___x_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4419_; 
lean_dec_ref(v___x_4415_);
lean_dec(v_i_4350_);
lean_inc(v_a_4356_);
lean_inc_ref(v_a_4355_);
lean_inc(v_a_4354_);
lean_inc_ref(v_a_4353_);
lean_inc(v_a_4352_);
lean_inc_ref(v_a_4351_);
v___x_4419_ = lean_apply_9(v_runInBase_4349_, lean_box(0), v_k_4348_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, lean_box(0));
return v___x_4419_;
}
else
{
lean_object* v___f_4420_; lean_object* v___f_4421_; lean_object* v___f_4422_; lean_object* v_x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___f_4426_; lean_object* v___x_4427_; 
v___f_4420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20));
v___f_4421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21));
v___f_4422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25);
v_x_4423_ = lean_array_fget_borrowed(v_xs_4347_, v_i_4350_);
v___x_4424_ = l_Lean_Expr_fvarId_x21(v_x_4423_);
v___x_4425_ = lean_unsigned_to_nat(100u);
v___f_4426_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed), 10, 2);
lean_closure_set(v___f_4426_, 0, v___x_4424_);
lean_closure_set(v___f_4426_, 1, v___x_4425_);
v___x_4427_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4426_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_4433_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4421_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4435_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v___x_4435_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4420_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; uint8_t v_hasTrace_4437_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v_hasTrace_4437_ = lean_ctor_get_uint8(v_a_4436_, sizeof(void*)*1);
if (v_hasTrace_4437_ == 0)
{
lean_dec(v_a_4436_);
lean_dec(v_a_4434_);
lean_dec_ref(v___x_4415_);
goto v___jp_4429_;
}
else
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28);
v___x_4439_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_a_4434_, v_a_4436_, v___x_4438_);
lean_dec(v_a_4436_);
lean_dec(v_a_4434_);
if (v___x_4439_ == 0)
{
lean_dec_ref(v___x_4415_);
goto v___jp_4429_;
}
else
{
lean_object* v_proof_4440_; lean_object* v___x_4441_; lean_object* v___y_4443_; 
v_proof_4440_ = lean_ctor_get(v_a_4428_, 2);
v___x_4441_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30);
switch(lean_obj_tag(v_proof_4440_))
{
case 0:
{
lean_object* v_declName_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v_declName_4457_ = lean_ctor_get(v_proof_4440_, 0);
v___x_4458_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32);
lean_inc(v_declName_4457_);
v___x_4459_ = l_Lean_MessageData_ofName(v_declName_4457_);
v___x_4460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
v___y_4443_ = v___x_4460_;
goto v___jp_4442_;
}
case 1:
{
lean_object* v_fvarId_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v_fvarId_4461_ = lean_ctor_get(v_proof_4440_, 0);
v___x_4462_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34);
lean_inc(v_fvarId_4461_);
v___x_4463_ = l_Lean_mkFVar(v_fvarId_4461_);
v___x_4464_ = l_Lean_MessageData_ofExpr(v___x_4463_);
v___x_4465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4462_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
v___y_4443_ = v___x_4465_;
goto v___jp_4442_;
}
default: 
{
lean_object* v_ref_4466_; lean_object* v_proof_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_ref_4466_ = lean_ctor_get(v_proof_4440_, 1);
v_proof_4467_ = lean_ctor_get(v_proof_4440_, 2);
v___x_4468_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36);
lean_inc(v_ref_4466_);
v___x_4469_ = l_Lean_MessageData_ofSyntax(v_ref_4466_);
v___x_4470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4468_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
v___x_4471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38);
v___x_4472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4470_);
lean_ctor_set(v___x_4472_, 1, v___x_4471_);
lean_inc_ref(v_proof_4467_);
v___x_4473_ = l_Lean_MessageData_ofExpr(v_proof_4467_);
v___x_4474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4472_);
lean_ctor_set(v___x_4474_, 1, v___x_4473_);
v___y_4443_ = v___x_4474_;
goto v___jp_4442_;
}
}
v___jp_4442_:
{
lean_object* v___x_4444_; lean_object* v___x_5552__overap_4445_; lean_object* v___x_4446_; 
v___x_4444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4441_);
lean_ctor_set(v___x_4444_, 1, v___y_4443_);
lean_inc_ref(v_toMonadRef_4373_);
v___x_5552__overap_4445_ = l_Lean_addTrace___redArg(v___x_4415_, v___x_4416_, v_toMonadRef_4373_, v___f_4422_, v___x_4432_, v___x_4444_);
lean_inc(v_a_4356_);
lean_inc_ref(v_a_4355_);
lean_inc(v_a_4354_);
lean_inc_ref(v_a_4353_);
lean_inc(v_a_4352_);
lean_inc_ref(v_a_4351_);
v___x_4446_ = lean_apply_7(v___x_5552__overap_4445_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, lean_box(0));
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4448_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
lean_inc_ref(v_runInBase_4349_);
lean_inc(v_k_4348_);
v___x_4448_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4350_, v_a_4428_, v_xs_4347_, v_k_4348_, v_runInBase_4349_, v_a_4447_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
v___y_4370_ = v___x_4448_;
goto v___jp_4369_;
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_a_4428_);
v_a_4449_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4446_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4446_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
lean_inc(v_a_4449_);
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
v___y_4359_ = v___x_4454_;
v_a_4360_ = v_a_4449_;
goto v___jp_4358_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4475_; 
lean_dec(v_a_4434_);
lean_dec(v_a_4428_);
lean_dec_ref(v___x_4415_);
v_a_4475_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4435_, 1);
v_a_4367_ = v_a_4475_;
goto v___jp_4366_;
}
}
else
{
lean_object* v_a_4476_; 
lean_dec(v_a_4428_);
lean_dec_ref(v___x_4415_);
v_a_4476_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4433_, 1);
v_a_4367_ = v_a_4476_;
goto v___jp_4366_;
}
v___jp_4429_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = lean_box(0);
lean_inc_ref(v_runInBase_4349_);
lean_inc(v_k_4348_);
v___x_4431_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4350_, v_a_4428_, v_xs_4347_, v_k_4348_, v_runInBase_4349_, v___x_4430_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
v___y_4370_ = v___x_4431_;
goto v___jp_4369_;
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec_ref(v___x_4415_);
v_a_4477_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4427_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4427_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
lean_inc(v_a_4477_);
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
v___y_4359_ = v___x_4482_;
v_a_4360_ = v_a_4477_;
goto v___jp_4358_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(lean_object* v_i_4491_, lean_object* v_a_4492_, lean_object* v_xs_4493_, lean_object* v_k_4494_, lean_object* v_runInBase_4495_, lean_object* v_____r_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_config_4504_; lean_object* v_specThms_4505_; lean_object* v_simpCtx_4506_; lean_object* v_simprocs_4507_; lean_object* v_jps_4508_; lean_object* v_initialCtxSize_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v_config_4504_ = lean_ctor_get(v___y_4497_, 0);
v_specThms_4505_ = lean_ctor_get(v___y_4497_, 1);
v_simpCtx_4506_ = lean_ctor_get(v___y_4497_, 2);
v_simprocs_4507_ = lean_ctor_get(v___y_4497_, 3);
v_jps_4508_ = lean_ctor_get(v___y_4497_, 4);
v_initialCtxSize_4509_ = lean_ctor_get(v___y_4497_, 5);
v___x_4510_ = lean_unsigned_to_nat(1u);
v___x_4511_ = lean_nat_add(v_i_4491_, v___x_4510_);
lean_inc_ref(v_specThms_4505_);
v___x_4512_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_specThms_4505_, v_a_4492_);
lean_inc(v_initialCtxSize_4509_);
lean_inc(v_jps_4508_);
lean_inc_ref(v_simprocs_4507_);
lean_inc_ref(v_simpCtx_4506_);
lean_inc_ref(v_config_4504_);
v___x_4513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4513_, 0, v_config_4504_);
lean_ctor_set(v___x_4513_, 1, v___x_4512_);
lean_ctor_set(v___x_4513_, 2, v_simpCtx_4506_);
lean_ctor_set(v___x_4513_, 3, v_simprocs_4507_);
lean_ctor_set(v___x_4513_, 4, v_jps_4508_);
lean_ctor_set(v___x_4513_, 5, v_initialCtxSize_4509_);
v___x_4514_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4493_, v_k_4494_, v_runInBase_4495_, v___x_4511_, v___x_4513_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
lean_dec_ref_known(v___x_4513_, 6);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3___boxed(lean_object* v_i_4515_, lean_object* v_a_4516_, lean_object* v_xs_4517_, lean_object* v_k_4518_, lean_object* v_runInBase_4519_, lean_object* v_____r_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4515_, v_a_4516_, v_xs_4517_, v_k_4518_, v_runInBase_4519_, v_____r_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec_ref(v_xs_4517_);
lean_dec(v_i_4515_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___boxed(lean_object* v_xs_4529_, lean_object* v_k_4530_, lean_object* v_runInBase_4531_, lean_object* v_i_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4529_, v_k_4530_, v_runInBase_4531_, v_i_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec_ref(v_xs_4529_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(lean_object* v_m_4541_, lean_object* v_00_u03b1_4542_, lean_object* v_inst_4543_, lean_object* v_xs_4544_, lean_object* v_k_4545_, lean_object* v_runInBase_4546_, lean_object* v_i_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4544_, v_k_4545_, v_runInBase_4546_, v_i_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___boxed(lean_object* v_m_4556_, lean_object* v_00_u03b1_4557_, lean_object* v_inst_4558_, lean_object* v_xs_4559_, lean_object* v_k_4560_, lean_object* v_runInBase_4561_, lean_object* v_i_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(v_m_4556_, v_00_u03b1_4557_, v_inst_4558_, v_xs_4559_, v_k_4560_, v_runInBase_4561_, v_i_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec_ref(v_xs_4559_);
lean_dec_ref(v_inst_4558_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter___redArg(lean_object* v_ex_4571_, lean_object* v_h__1_4572_, lean_object* v_h__2_4573_){
_start:
{
if (lean_obj_tag(v_ex_4571_) == 0)
{
lean_object* v_ref_4574_; lean_object* v_msg_4575_; lean_object* v___x_4576_; 
lean_dec(v_h__1_4572_);
v_ref_4574_ = lean_ctor_get(v_ex_4571_, 0);
lean_inc(v_ref_4574_);
v_msg_4575_ = lean_ctor_get(v_ex_4571_, 1);
lean_inc_ref(v_msg_4575_);
lean_dec_ref_known(v_ex_4571_, 2);
v___x_4576_ = lean_apply_2(v_h__2_4573_, v_ref_4574_, v_msg_4575_);
return v___x_4576_;
}
else
{
lean_object* v_id_4577_; lean_object* v_extra_4578_; lean_object* v___x_4579_; 
lean_dec(v_h__2_4573_);
v_id_4577_ = lean_ctor_get(v_ex_4571_, 0);
lean_inc(v_id_4577_);
v_extra_4578_ = lean_ctor_get(v_ex_4571_, 1);
lean_inc(v_extra_4578_);
lean_dec_ref_known(v_ex_4571_, 2);
v___x_4579_ = lean_apply_2(v_h__1_4572_, v_id_4577_, v_extra_4578_);
return v___x_4579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter(lean_object* v_motive_4580_, lean_object* v_ex_4581_, lean_object* v_h__1_4582_, lean_object* v_h__2_4583_){
_start:
{
if (lean_obj_tag(v_ex_4581_) == 0)
{
lean_object* v_ref_4584_; lean_object* v_msg_4585_; lean_object* v___x_4586_; 
lean_dec(v_h__1_4582_);
v_ref_4584_ = lean_ctor_get(v_ex_4581_, 0);
lean_inc(v_ref_4584_);
v_msg_4585_ = lean_ctor_get(v_ex_4581_, 1);
lean_inc_ref(v_msg_4585_);
lean_dec_ref_known(v_ex_4581_, 2);
v___x_4586_ = lean_apply_2(v_h__2_4583_, v_ref_4584_, v_msg_4585_);
return v___x_4586_;
}
else
{
lean_object* v_id_4587_; lean_object* v_extra_4588_; lean_object* v___x_4589_; 
lean_dec(v_h__2_4583_);
v_id_4587_ = lean_ctor_get(v_ex_4581_, 0);
lean_inc(v_id_4587_);
v_extra_4588_ = lean_ctor_get(v_ex_4581_, 1);
lean_inc(v_extra_4588_);
lean_dec_ref_known(v_ex_4581_, 2);
v___x_4589_ = lean_apply_2(v_h__1_4582_, v_id_4587_, v_extra_4588_);
return v___x_4589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(lean_object* v_xs_4590_, lean_object* v_k_4591_, lean_object* v_runInBase_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4600_ = lean_unsigned_to_nat(0u);
v___x_4601_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4590_, v_k_4591_, v_runInBase_4592_, v___x_4600_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed(lean_object* v_xs_4602_, lean_object* v_k_4603_, lean_object* v_runInBase_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(v_xs_4602_, v_k_4603_, v_runInBase_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec_ref(v_xs_4602_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(lean_object* v_inst_4613_, lean_object* v_inst_4614_, lean_object* v_xs_4615_, lean_object* v_k_4616_){
_start:
{
lean_object* v_toBind_4617_; lean_object* v_liftWith_4618_; lean_object* v_restoreM_4619_; lean_object* v___f_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v_toBind_4617_ = lean_ctor_get(v_inst_4613_, 1);
lean_inc(v_toBind_4617_);
lean_dec_ref(v_inst_4613_);
v_liftWith_4618_ = lean_ctor_get(v_inst_4614_, 0);
lean_inc(v_liftWith_4618_);
v_restoreM_4619_ = lean_ctor_get(v_inst_4614_, 1);
lean_inc(v_restoreM_4619_);
lean_dec_ref(v_inst_4614_);
v___f_4620_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4620_, 0, v_xs_4615_);
lean_closure_set(v___f_4620_, 1, v_k_4616_);
v___x_4621_ = lean_apply_2(v_liftWith_4618_, lean_box(0), v___f_4620_);
v___x_4622_ = lean_apply_1(v_restoreM_4619_, lean_box(0));
v___x_4623_ = lean_apply_4(v_toBind_4617_, lean_box(0), lean_box(0), v___x_4621_, v___x_4622_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs(lean_object* v_m_4624_, lean_object* v_00_u03b1_4625_, lean_object* v_inst_4626_, lean_object* v_inst_4627_, lean_object* v_xs_4628_, lean_object* v_k_4629_){
_start:
{
lean_object* v___x_4630_; 
v___x_4630_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(v_inst_4626_, v_inst_4627_, v_xs_4628_, v_k_4629_);
return v___x_4630_;
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
