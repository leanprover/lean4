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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object*);
lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 186, 72, 71, 180, 239, 13, 70)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 197, 164, 82, 155, 28, 143, 213)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "disable `mvcgen` usage warning"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(217, 19, 39, 228, 182, 81, 226, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 41, 69, 108, 13, 191, 254, 76)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mvcgen_warning;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(lean_object* v_name_123_, lean_object* v_decl_124_, lean_object* v_ref_125_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_151_, lean_object* v_decl_152_, lean_object* v_ref_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(v_name_151_, v_decl_152_, v_ref_153_);
lean_dec_ref(v_decl_152_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_));
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_));
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_));
v___x_178_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4__spec__0(v___x_175_, v___x_176_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4____boxed(lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_();
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx(lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(0u);
return v___x_182_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(1u);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorIdx___boxed(lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Elab_Tactic_Do_Fuel_ctorIdx(v_x_184_);
lean_dec(v_x_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(lean_object* v_t_186_, lean_object* v_k_187_){
_start:
{
if (lean_obj_tag(v_t_186_) == 0)
{
lean_object* v_n_188_; lean_object* v___x_189_; 
v_n_188_ = lean_ctor_get(v_t_186_, 0);
lean_inc(v_n_188_);
lean_dec_ref_known(v_t_186_, 1);
v___x_189_ = lean_apply_1(v_k_187_, v_n_188_);
return v___x_189_;
}
else
{
return v_k_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim(lean_object* v_motive_190_, lean_object* v_ctorIdx_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_k_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_192_, v_k_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_ctorElim___boxed(lean_object* v_motive_196_, lean_object* v_ctorIdx_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_k_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim(v_motive_196_, v_ctorIdx_197_, v_t_198_, v_h_199_, v_k_200_);
lean_dec(v_ctorIdx_197_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim___redArg(lean_object* v_t_202_, lean_object* v_limited_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_202_, v_limited_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_limited_elim(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_limited_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_206_, v_limited_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim___redArg(lean_object* v_t_210_, lean_object* v_unlimited_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_210_, v_unlimited_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Fuel_unlimited_elim(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_unlimited_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Elab_Tactic_Do_Fuel_ctorElim___redArg(v_t_214_, v_unlimited_216_);
return v___x_217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v_n_220_; lean_object* v_n_221_; uint8_t v___x_222_; 
v_n_220_ = lean_ctor_get(v_x_218_, 0);
v_n_221_ = lean_ctor_get(v_x_219_, 0);
v___x_222_ = lean_nat_dec_eq(v_n_220_, v_n_221_);
return v___x_222_;
}
else
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
}
else
{
if (lean_obj_tag(v_x_219_) == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
else
{
uint8_t v___x_225_; 
v___x_225_ = 1;
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq___boxed(lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_226_, v_x_227_);
lean_dec(v_x_227_);
lean_dec(v_x_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instDecidableEqFuel(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel_decEq(v_x_230_, v_x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instDecidableEqFuel___boxed(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Lean_Elab_Tactic_Do_instDecidableEqFuel(v_x_233_, v_x_234_);
lean_dec(v_x_234_);
lean_dec(v_x_233_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_box(0);
v___x_238_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(lean_object* v_00_u03b1_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___boxed(lean_object* v_00_u03b1_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(lean_object* v_msgData_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; lean_object* v_env_266_; lean_object* v___x_267_; lean_object* v_mctx_268_; lean_object* v_lctx_269_; lean_object* v_options_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_265_ = lean_st_ref_get(v___y_263_);
v_env_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc_ref(v_env_266_);
lean_dec(v___x_265_);
v___x_267_ = lean_st_ref_get(v___y_261_);
v_mctx_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_mctx_268_);
lean_dec(v___x_267_);
v_lctx_269_ = lean_ctor_get(v___y_260_, 2);
v_options_270_ = lean_ctor_get(v___y_262_, 2);
lean_inc_ref(v_options_270_);
lean_inc_ref(v_lctx_269_);
v___x_271_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_271_, 0, v_env_266_);
lean_ctor_set(v___x_271_, 1, v_mctx_268_);
lean_ctor_set(v___x_271_, 2, v_lctx_269_);
lean_ctor_set(v___x_271_, 3, v_options_270_);
v___x_272_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_msgData_259_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1___boxed(lean_object* v_msgData_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msgData_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(lean_object* v_msg_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_ref_287_; lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
v_ref_287_ = lean_ctor_get(v___y_284_, 5);
v___x_288_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_297_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_inc(v_ref_287_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_ref_287_);
lean_ctor_set(v___x_293_, 1, v_a_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 1);
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__1));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(lean_object* v___x_309_, lean_object* v___x_310_, lean_object* v_ctor_311_, lean_object* v_args_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__0));
v___x_432_ = lean_string_dec_eq(v_ctor_311_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v___x_310_);
v___x_433_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__0___redArg();
return v___x_433_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_434_ = lean_array_get_size(v_args_312_);
v___x_435_ = lean_unsigned_to_nat(8u);
v___x_436_ = lean_nat_dec_eq(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v___x_310_);
v___x_437_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___closed__2);
v___x_438_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_437_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
goto v___jp_318_;
}
}
v___jp_318_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_319_);
lean_inc(v___x_320_);
v___x_321_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_320_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_323_);
lean_inc(v___x_324_);
v___x_325_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_324_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_327_);
lean_inc(v___x_328_);
v___x_329_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_328_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = lean_unsigned_to_nat(3u);
v___x_332_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_331_);
lean_inc(v___x_332_);
v___x_333_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_332_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_evalExpr_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v_evalExpr_335_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref(v_evalExpr_335_);
lean_dec_ref(v___x_310_);
v___x_336_ = lean_unsigned_to_nat(4u);
v___x_337_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_336_);
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
lean_inc(v___y_314_);
lean_inc_ref(v___y_313_);
lean_inc(v___x_337_);
v___x_338_ = lean_apply_6(v_evalExpr_335_, v___x_337_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, lean_box(0));
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v___x_340_ = lean_unsigned_to_nat(5u);
v___x_341_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_340_);
lean_inc(v___x_341_);
v___x_342_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_341_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = lean_unsigned_to_nat(6u);
v___x_345_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_344_);
lean_inc(v___x_345_);
v___x_346_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_345_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = lean_unsigned_to_nat(7u);
v___x_349_ = lean_array_get_borrowed(v___x_309_, v_args_312_, v___x_348_);
lean_inc(v___x_349_);
v___x_350_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v___x_349_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_366_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_366_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_366_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_366_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; uint8_t v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; uint8_t v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; uint8_t v___x_362_; lean_object* v___x_364_; 
v___x_355_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v___x_355_, 0, v_a_339_);
v___x_356_ = lean_unbox(v_a_322_);
lean_dec(v_a_322_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_356_);
v___x_357_ = lean_unbox(v_a_326_);
lean_dec(v_a_326_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1 + 1, v___x_357_);
v___x_358_ = lean_unbox(v_a_330_);
lean_dec(v_a_330_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1 + 2, v___x_358_);
v___x_359_ = lean_unbox(v_a_334_);
lean_dec(v_a_334_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1 + 3, v___x_359_);
v___x_360_ = lean_unbox(v_a_343_);
lean_dec(v_a_343_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1 + 4, v___x_360_);
v___x_361_ = lean_unbox(v_a_347_);
lean_dec(v_a_347_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1 + 5, v___x_361_);
v___x_362_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1 + 6, v___x_362_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_364_ = v___x_353_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_355_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_a_347_);
lean_dec(v_a_343_);
lean_dec(v_a_339_);
lean_dec(v_a_334_);
lean_dec(v_a_330_);
lean_dec(v_a_326_);
lean_dec(v_a_322_);
v_a_367_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_350_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_350_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_a_343_);
lean_dec(v_a_339_);
lean_dec(v_a_334_);
lean_dec(v_a_330_);
lean_dec(v_a_326_);
lean_dec(v_a_322_);
v_a_375_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_346_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_346_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_a_339_);
lean_dec(v_a_334_);
lean_dec(v_a_330_);
lean_dec(v_a_326_);
lean_dec(v_a_322_);
v_a_383_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_342_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_342_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_a_334_);
lean_dec(v_a_330_);
lean_dec(v_a_326_);
lean_dec(v_a_322_);
v_a_391_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_338_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_338_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_a_330_);
lean_dec(v_a_326_);
lean_dec(v_a_322_);
lean_dec_ref(v___x_310_);
v_a_399_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_333_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_333_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_a_326_);
lean_dec(v_a_322_);
lean_dec_ref(v___x_310_);
v_a_407_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_329_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_329_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_a_322_);
lean_dec_ref(v___x_310_);
v_a_415_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_325_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_325_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v___x_310_);
v_a_423_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_321_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_321_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___boxed(lean_object* v___x_447_, lean_object* v___x_448_, lean_object* v_ctor_449_, lean_object* v_args_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0(v___x_447_, v___x_448_, v_ctor_449_, v_args_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec_ref(v_args_450_);
lean_dec_ref(v_ctor_449_);
lean_dec_ref(v___x_447_);
return v_res_456_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_458_ = l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___f_461_; 
v___x_459_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0);
v___x_460_ = l_Lean_instInhabitedExpr;
v___f_461_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___lam__0___boxed), 9, 2);
lean_closure_set(v___f_461_, 0, v___x_460_);
lean_closure_set(v___f_461_, 1, v___x_459_);
return v___f_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___f_476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__1);
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_478_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(v___x_477_, v___f_476_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___boxed(lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(lean_object* v_00_u03b1_486_, lean_object* v_msg_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___boxed(lean_object* v_00_u03b1_494_, lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_494_, v_msg_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_box(0);
v___x_504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_505_ = l_Lean_Expr_const___override(v___x_504_, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1);
v___x_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2);
v___x_509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__0));
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__3);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(lean_object* v_e_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_Expr_hasMVar(v_e_512_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_e_512_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v_mctx_518_; lean_object* v___x_519_; lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v___x_522_; lean_object* v_cache_523_; lean_object* v_zetaDeltaFVarIds_524_; lean_object* v_postponed_525_; lean_object* v_diag_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_535_; 
v___x_517_ = lean_st_ref_get(v___y_513_);
v_mctx_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_mctx_518_);
lean_dec(v___x_517_);
v___x_519_ = l_Lean_instantiateMVarsCore(v_mctx_518_, v_e_512_);
v_fst_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_fst_520_);
v_snd_521_ = lean_ctor_get(v___x_519_, 1);
lean_inc(v_snd_521_);
lean_dec_ref(v___x_519_);
v___x_522_ = lean_st_ref_take(v___y_513_);
v_cache_523_ = lean_ctor_get(v___x_522_, 1);
v_zetaDeltaFVarIds_524_ = lean_ctor_get(v___x_522_, 2);
v_postponed_525_ = lean_ctor_get(v___x_522_, 3);
v_diag_526_ = lean_ctor_get(v___x_522_, 4);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; 
v_unused_536_ = lean_ctor_get(v___x_522_, 0);
lean_dec(v_unused_536_);
v___x_528_ = v___x_522_;
v_isShared_529_ = v_isSharedCheck_535_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_diag_526_);
lean_inc(v_postponed_525_);
lean_inc(v_zetaDeltaFVarIds_524_);
lean_inc(v_cache_523_);
lean_dec(v___x_522_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_535_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v_snd_521_);
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_snd_521_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_cache_523_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_zetaDeltaFVarIds_524_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_postponed_525_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v_diag_526_);
v___x_531_ = v_reuseFailAlloc_534_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_st_ref_put(v___y_513_, v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v_fst_520_);
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg___boxed(lean_object* v_e_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_e_537_, v___y_538_);
lean_dec(v___y_538_);
return v_res_540_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
v___x_542_ = l_Lean_Elab_abortTermExceptionId;
v___x_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg(){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___closed__0);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg___boxed(lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
return v_res_548_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_box(1);
v___x_550_ = l_Lean_MessageData_ofFormat(v___x_549_);
return v___x_550_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__2));
v___x_555_ = l_Lean_MessageData_ofFormat(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
return v_x_556_;
}
else
{
lean_object* v_head_558_; lean_object* v_tail_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_581_; 
v_head_558_ = lean_ctor_get(v_x_557_, 0);
v_tail_559_ = lean_ctor_get(v_x_557_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_581_ == 0)
{
v___x_561_ = v_x_557_;
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_tail_559_);
lean_inc(v_head_558_);
lean_dec(v_x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_before_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_579_; 
v_before_563_ = lean_ctor_get(v_head_558_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_head_558_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v_head_558_, 1);
lean_dec(v_unused_580_);
v___x_565_ = v_head_558_;
v_isShared_566_ = v_isSharedCheck_579_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_before_563_);
lean_dec(v_head_558_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_579_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 7);
lean_ctor_set(v___x_565_, 1, v___x_567_);
lean_ctor_set(v___x_565_, 0, v_x_556_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_x_556_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_578_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__3);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 7);
lean_ctor_set(v___x_561_, 1, v___x_570_);
lean_ctor_set(v___x_561_, 0, v___x_569_);
v___x_572_ = v___x_561_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_577_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = l_Lean_MessageData_ofSyntax(v_before_563_);
v___x_574_ = l_Lean_indentD(v___x_573_);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_572_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v_x_556_ = v___x_575_;
v_x_557_ = v_tail_559_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(lean_object* v_opts_582_, lean_object* v_opt_583_){
_start:
{
lean_object* v_name_584_; lean_object* v_defValue_585_; lean_object* v_map_586_; lean_object* v___x_587_; 
v_name_584_ = lean_ctor_get(v_opt_583_, 0);
v_defValue_585_ = lean_ctor_get(v_opt_583_, 1);
v_map_586_ = lean_ctor_get(v_opts_582_, 0);
v___x_587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_586_, v_name_584_);
if (lean_obj_tag(v___x_587_) == 0)
{
uint8_t v___x_588_; 
v___x_588_ = lean_unbox(v_defValue_585_);
return v___x_588_;
}
else
{
lean_object* v_val_589_; 
v_val_589_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v___x_587_, 1);
if (lean_obj_tag(v_val_589_) == 1)
{
uint8_t v_v_590_; 
v_v_590_ = lean_ctor_get_uint8(v_val_589_, 0);
lean_dec_ref_known(v_val_589_, 0);
return v_v_590_;
}
else
{
uint8_t v___x_591_; 
lean_dec(v_val_589_);
v___x_591_ = lean_unbox(v_defValue_585_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6___boxed(lean_object* v_opts_592_, lean_object* v_opt_593_){
_start:
{
uint8_t v_res_594_; lean_object* v_r_595_; 
v_res_594_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(v_opts_592_, v_opt_593_);
lean_dec_ref(v_opt_593_);
lean_dec_ref(v_opts_592_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__1));
v___x_600_ = l_Lean_MessageData_ofFormat(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(lean_object* v_msgData_601_, lean_object* v_macroStack_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_options_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_options_605_ = lean_ctor_get(v___y_603_, 2);
v___x_606_ = l_Lean_Elab_pp_macroStack;
v___x_607_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__6(v_options_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec(v_macroStack_602_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v_msgData_601_);
return v___x_608_;
}
else
{
if (lean_obj_tag(v_macroStack_602_) == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_msgData_601_);
return v___x_609_;
}
else
{
lean_object* v_head_610_; lean_object* v_after_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_626_; 
v_head_610_ = lean_ctor_get(v_macroStack_602_, 0);
lean_inc(v_head_610_);
v_after_611_ = lean_ctor_get(v_head_610_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_head_610_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v_head_610_, 0);
lean_dec(v_unused_627_);
v___x_613_ = v_head_610_;
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_after_611_);
lean_dec(v_head_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7___closed__0);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 7);
lean_ctor_set(v___x_613_, 1, v___x_615_);
lean_ctor_set(v___x_613_, 0, v_msgData_601_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_msgData_601_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_615_);
v___x_617_ = v_reuseFailAlloc_625_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_msgData_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_618_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___closed__2);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_MessageData_ofSyntax(v_after_611_);
v___x_621_ = l_Lean_indentD(v___x_620_);
v_msgData_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_622_, 0, v___x_619_);
lean_ctor_set(v_msgData_622_, 1, v___x_621_);
v___x_623_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4_spec__7(v_msgData_622_, v_macroStack_602_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_628_, lean_object* v_macroStack_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_msgData_628_, v_macroStack_629_, v___y_630_);
lean_dec_ref(v___y_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_ref_641_; lean_object* v___x_642_; lean_object* v_a_643_; lean_object* v_macroStack_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
v_ref_641_ = lean_ctor_get(v___y_638_, 5);
v___x_642_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_633_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref(v___x_642_);
v_macroStack_644_ = lean_ctor_get(v___y_634_, 1);
v___x_645_ = l_Lean_Elab_getBetterRef(v_ref_641_, v_macroStack_644_);
lean_inc(v_macroStack_644_);
v___x_646_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_a_643_, v_macroStack_644_, v___y_638_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_655_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_645_);
lean_ctor_set(v___x_651_, 1, v_a_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 1);
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg___boxed(lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v_msg_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
return v_res_664_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__0));
v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__2));
v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__4));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__6));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__8));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(lean_object* v_stx_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_evalExpr_689_; lean_object* v_expectedType_x3f_690_; uint8_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_fileName_696_; lean_object* v_fileMap_697_; lean_object* v_options_698_; lean_object* v_currRecDepth_699_; lean_object* v_maxRecDepth_700_; lean_object* v_ref_701_; lean_object* v_currNamespace_702_; lean_object* v_openDecls_703_; lean_object* v_initHeartbeats_704_; lean_object* v_maxHeartbeats_705_; lean_object* v_quotContext_706_; lean_object* v_currMacroScope_707_; uint8_t v_diag_708_; lean_object* v_cancelTk_x3f_709_; uint8_t v_suppressElabErrors_710_; lean_object* v_inheritedTraceOptions_711_; uint8_t v___x_712_; lean_object* v_ref_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_688_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__0);
v_evalExpr_689_ = lean_ctor_get(v___x_688_, 0);
v_expectedType_x3f_690_ = lean_ctor_get(v___x_688_, 1);
v___x_691_ = 1;
v___x_692_ = lean_box(0);
v___x_693_ = lean_box(v___x_691_);
v___x_694_ = lean_box(v___x_691_);
lean_inc(v_expectedType_x3f_690_);
lean_inc(v_stx_680_);
v___x_695_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_695_, 0, v_stx_680_);
lean_closure_set(v___x_695_, 1, v_expectedType_x3f_690_);
lean_closure_set(v___x_695_, 2, v___x_693_);
lean_closure_set(v___x_695_, 3, v___x_694_);
lean_closure_set(v___x_695_, 4, v___x_692_);
v_fileName_696_ = lean_ctor_get(v_a_685_, 0);
v_fileMap_697_ = lean_ctor_get(v_a_685_, 1);
v_options_698_ = lean_ctor_get(v_a_685_, 2);
v_currRecDepth_699_ = lean_ctor_get(v_a_685_, 3);
v_maxRecDepth_700_ = lean_ctor_get(v_a_685_, 4);
v_ref_701_ = lean_ctor_get(v_a_685_, 5);
v_currNamespace_702_ = lean_ctor_get(v_a_685_, 6);
v_openDecls_703_ = lean_ctor_get(v_a_685_, 7);
v_initHeartbeats_704_ = lean_ctor_get(v_a_685_, 8);
v_maxHeartbeats_705_ = lean_ctor_get(v_a_685_, 9);
v_quotContext_706_ = lean_ctor_get(v_a_685_, 10);
v_currMacroScope_707_ = lean_ctor_get(v_a_685_, 11);
v_diag_708_ = lean_ctor_get_uint8(v_a_685_, sizeof(void*)*14);
v_cancelTk_x3f_709_ = lean_ctor_get(v_a_685_, 12);
v_suppressElabErrors_710_ = lean_ctor_get_uint8(v_a_685_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_711_ = lean_ctor_get(v_a_685_, 13);
v___x_712_ = 1;
v_ref_713_ = l_Lean_replaceRef(v_stx_680_, v_ref_701_);
lean_dec(v_stx_680_);
lean_inc_ref(v_inheritedTraceOptions_711_);
lean_inc(v_cancelTk_x3f_709_);
lean_inc(v_currMacroScope_707_);
lean_inc(v_quotContext_706_);
lean_inc(v_maxHeartbeats_705_);
lean_inc(v_initHeartbeats_704_);
lean_inc(v_openDecls_703_);
lean_inc(v_currNamespace_702_);
lean_inc(v_maxRecDepth_700_);
lean_inc(v_currRecDepth_699_);
lean_inc_ref(v_options_698_);
lean_inc_ref(v_fileMap_697_);
lean_inc_ref(v_fileName_696_);
v___x_714_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_714_, 0, v_fileName_696_);
lean_ctor_set(v___x_714_, 1, v_fileMap_697_);
lean_ctor_set(v___x_714_, 2, v_options_698_);
lean_ctor_set(v___x_714_, 3, v_currRecDepth_699_);
lean_ctor_set(v___x_714_, 4, v_maxRecDepth_700_);
lean_ctor_set(v___x_714_, 5, v_ref_713_);
lean_ctor_set(v___x_714_, 6, v_currNamespace_702_);
lean_ctor_set(v___x_714_, 7, v_openDecls_703_);
lean_ctor_set(v___x_714_, 8, v_initHeartbeats_704_);
lean_ctor_set(v___x_714_, 9, v_maxHeartbeats_705_);
lean_ctor_set(v___x_714_, 10, v_quotContext_706_);
lean_ctor_set(v___x_714_, 11, v_currMacroScope_707_);
lean_ctor_set(v___x_714_, 12, v_cancelTk_x3f_709_);
lean_ctor_set(v___x_714_, 13, v_inheritedTraceOptions_711_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*14, v_diag_708_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*14 + 1, v_suppressElabErrors_710_);
v___x_715_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_695_, v___x_712_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v___x_714_, v_a_686_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v_a_718_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v___y_742_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___x_827_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_a_716_, v_a_684_);
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
v___x_827_ = l_Lean_Expr_hasSorry(v_a_718_);
if (v___x_827_ == 0)
{
v___y_772_ = v_a_681_;
v___y_773_ = v_a_682_;
v___y_774_ = v_a_683_;
v___y_775_ = v_a_684_;
v___y_776_ = v___x_714_;
v___y_777_ = v_a_686_;
goto v___jp_771_;
}
else
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_Expr_hasSyntheticSorry(v_a_718_);
if (v___x_828_ == 0)
{
v___y_809_ = v_a_681_;
v___y_810_ = v_a_682_;
v___y_811_ = v_a_683_;
v___y_812_ = v_a_684_;
v___y_813_ = v___x_714_;
v___y_814_ = v_a_686_;
goto v___jp_808_;
}
else
{
lean_object* v___x_829_; lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_a_718_);
lean_dec_ref_known(v___x_714_, 14);
v___x_829_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
v___jp_719_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_727_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1);
v___x_728_ = l_Lean_indentExpr(v_a_718_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___y_726_);
v___x_731_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_730_, v___y_720_, v___y_721_, v___y_723_, v___y_722_, v___y_724_, v___y_725_);
lean_dec_ref(v___y_724_);
return v___x_731_;
}
v___jp_732_:
{
if (v___y_742_ == 0)
{
if (lean_obj_tag(v___y_736_) == 0)
{
lean_dec_ref_known(v___y_736_, 2);
lean_dec_ref(v___y_738_);
lean_dec(v_a_718_);
return v___y_739_;
}
else
{
lean_object* v_id_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_757_; 
v_id_743_ = lean_ctor_get(v___y_736_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___y_736_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___y_736_, 1);
lean_dec(v_unused_758_);
v___x_745_ = v___y_736_;
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_id_743_);
lean_dec(v___y_736_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; 
v___x_747_ = l_Lean_instBEqInternalExceptionId_beq(v___y_741_, v_id_743_);
lean_dec(v_id_743_);
if (v___x_747_ == 0)
{
lean_del_object(v___x_745_);
lean_dec_ref(v___y_738_);
lean_dec(v_a_718_);
return v___y_739_;
}
else
{
lean_dec_ref(v___y_739_);
if (lean_obj_tag(v_expectedType_x3f_690_) == 1)
{
lean_object* v_val_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v_val_748_ = lean_ctor_get(v_expectedType_x3f_690_, 0);
v___x_749_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3);
lean_inc(v_val_748_);
v___x_750_ = l_Lean_MessageData_ofExpr(v_val_748_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 7);
lean_ctor_set(v___x_745_, 1, v___x_750_);
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_752_ = v___x_745_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_750_);
v___x_752_ = v_reuseFailAlloc_755_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___y_720_ = v___y_733_;
v___y_721_ = v___y_734_;
v___y_722_ = v___y_735_;
v___y_723_ = v___y_737_;
v___y_724_ = v___y_738_;
v___y_725_ = v___y_740_;
v___y_726_ = v___x_754_;
goto v___jp_719_;
}
}
else
{
lean_object* v___x_756_; 
lean_del_object(v___x_745_);
v___x_756_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__7);
v___y_720_ = v___y_733_;
v___y_721_ = v___y_734_;
v___y_722_ = v___y_735_;
v___y_723_ = v___y_737_;
v___y_724_ = v___y_738_;
v___y_725_ = v___y_740_;
v___y_726_ = v___x_756_;
goto v___jp_719_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_736_);
lean_dec(v_a_718_);
return v___y_739_;
}
}
v___jp_759_:
{
lean_object* v___x_766_; 
lean_inc_ref(v_evalExpr_689_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v_a_718_);
v___x_766_ = lean_apply_6(v_evalExpr_689_, v_a_718_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, lean_box(0));
if (lean_obj_tag(v___x_766_) == 0)
{
lean_dec_ref(v___y_764_);
lean_dec(v_a_718_);
return v___x_766_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
v___x_768_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_769_ = l_Lean_Exception_isInterrupt(v_a_767_);
if (v___x_769_ == 0)
{
uint8_t v___x_770_; 
lean_inc(v_a_767_);
v___x_770_ = l_Lean_Exception_isRuntime(v_a_767_);
v___y_733_ = v___y_760_;
v___y_734_ = v___y_761_;
v___y_735_ = v___y_763_;
v___y_736_ = v_a_767_;
v___y_737_ = v___y_762_;
v___y_738_ = v___y_764_;
v___y_739_ = v___x_766_;
v___y_740_ = v___y_765_;
v___y_741_ = v___x_768_;
v___y_742_ = v___x_770_;
goto v___jp_732_;
}
else
{
v___y_733_ = v___y_760_;
v___y_734_ = v___y_761_;
v___y_735_ = v___y_763_;
v___y_736_ = v_a_767_;
v___y_737_ = v___y_762_;
v___y_738_ = v___y_764_;
v___y_739_ = v___x_766_;
v___y_740_ = v___y_765_;
v___y_741_ = v___x_768_;
v___y_742_ = v___x_769_;
goto v___jp_732_;
}
}
}
v___jp_771_:
{
lean_object* v___x_778_; 
lean_inc(v_a_718_);
v___x_778_ = l_Lean_Meta_getMVars(v_a_718_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_779_, v___x_692_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v_a_779_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; uint8_t v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v___x_782_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
if (v___x_782_ == 0)
{
v___y_760_ = v___y_772_;
v___y_761_ = v___y_773_;
v___y_762_ = v___y_774_;
v___y_763_ = v___y_775_;
v___y_764_ = v___y_776_;
v___y_765_ = v___y_777_;
goto v___jp_759_;
}
else
{
lean_object* v___x_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v___y_776_);
lean_dec(v_a_718_);
v___x_783_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v___y_776_);
lean_dec(v_a_718_);
v_a_792_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_780_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_780_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___y_776_);
lean_dec(v_a_718_);
v_a_800_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_778_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_778_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
v___jp_808_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
v___x_815_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9);
v___x_816_ = l_Lean_indentExpr(v_a_718_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_817_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___y_813_);
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
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
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref_known(v___x_714_, 14);
v_a_838_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_715_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_715_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___boxed(lean_object* v_stx_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(v_stx_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_box(0);
v___x_859_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__1));
v___x_860_ = l_Lean_mkConst(v___x_859_, v___x_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(lean_object* v_stx_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_fileName_870_; lean_object* v_fileMap_871_; lean_object* v_options_872_; lean_object* v_currRecDepth_873_; lean_object* v_maxRecDepth_874_; lean_object* v_ref_875_; lean_object* v_currNamespace_876_; lean_object* v_openDecls_877_; lean_object* v_initHeartbeats_878_; lean_object* v_maxHeartbeats_879_; lean_object* v_quotContext_880_; lean_object* v_currMacroScope_881_; uint8_t v_diag_882_; lean_object* v_cancelTk_x3f_883_; uint8_t v_suppressElabErrors_884_; lean_object* v_inheritedTraceOptions_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_ref_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_fileName_870_ = lean_ctor_get(v_a_867_, 0);
v_fileMap_871_ = lean_ctor_get(v_a_867_, 1);
v_options_872_ = lean_ctor_get(v_a_867_, 2);
v_currRecDepth_873_ = lean_ctor_get(v_a_867_, 3);
v_maxRecDepth_874_ = lean_ctor_get(v_a_867_, 4);
v_ref_875_ = lean_ctor_get(v_a_867_, 5);
v_currNamespace_876_ = lean_ctor_get(v_a_867_, 6);
v_openDecls_877_ = lean_ctor_get(v_a_867_, 7);
v_initHeartbeats_878_ = lean_ctor_get(v_a_867_, 8);
v_maxHeartbeats_879_ = lean_ctor_get(v_a_867_, 9);
v_quotContext_880_ = lean_ctor_get(v_a_867_, 10);
v_currMacroScope_881_ = lean_ctor_get(v_a_867_, 11);
v_diag_882_ = lean_ctor_get_uint8(v_a_867_, sizeof(void*)*14);
v_cancelTk_x3f_883_ = lean_ctor_get(v_a_867_, 12);
v_suppressElabErrors_884_ = lean_ctor_get_uint8(v_a_867_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_885_ = lean_ctor_get(v_a_867_, 13);
v___x_886_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2, &l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__2);
v___x_887_ = ((lean_object*)(l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___closed__3));
v_ref_888_ = l_Lean_replaceRef(v_stx_862_, v_ref_875_);
lean_inc_ref(v_inheritedTraceOptions_885_);
lean_inc(v_cancelTk_x3f_883_);
lean_inc(v_currMacroScope_881_);
lean_inc(v_quotContext_880_);
lean_inc(v_maxHeartbeats_879_);
lean_inc(v_initHeartbeats_878_);
lean_inc(v_openDecls_877_);
lean_inc(v_currNamespace_876_);
lean_inc(v_maxRecDepth_874_);
lean_inc(v_currRecDepth_873_);
lean_inc_ref(v_options_872_);
lean_inc_ref(v_fileMap_871_);
lean_inc_ref(v_fileName_870_);
v___x_889_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_889_, 0, v_fileName_870_);
lean_ctor_set(v___x_889_, 1, v_fileMap_871_);
lean_ctor_set(v___x_889_, 2, v_options_872_);
lean_ctor_set(v___x_889_, 3, v_currRecDepth_873_);
lean_ctor_set(v___x_889_, 4, v_maxRecDepth_874_);
lean_ctor_set(v___x_889_, 5, v_ref_888_);
lean_ctor_set(v___x_889_, 6, v_currNamespace_876_);
lean_ctor_set(v___x_889_, 7, v_openDecls_877_);
lean_ctor_set(v___x_889_, 8, v_initHeartbeats_878_);
lean_ctor_set(v___x_889_, 9, v_maxHeartbeats_879_);
lean_ctor_set(v___x_889_, 10, v_quotContext_880_);
lean_ctor_set(v___x_889_, 11, v_currMacroScope_881_);
lean_ctor_set(v___x_889_, 12, v_cancelTk_x3f_883_);
lean_ctor_set(v___x_889_, 13, v_inheritedTraceOptions_885_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*14, v_diag_882_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*14 + 1, v_suppressElabErrors_884_);
lean_inc(v_stx_862_);
v___x_890_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v___x_886_, v___x_887_, v_stx_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v___x_889_, v_a_868_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref_known(v___x_889_, 14);
lean_dec(v_stx_862_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_899_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_fst_895_; lean_object* v___x_897_; 
v_fst_895_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_fst_895_);
lean_dec(v_a_891_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v_fst_895_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_fst_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_915_; 
v_a_900_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_915_ == 0)
{
v___x_902_ = v___x_890_;
v_isShared_903_ = v_isSharedCheck_915_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_890_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_915_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_a_900_);
if (v_isShared_903_ == 0)
{
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_900_);
v___x_906_ = v_reuseFailAlloc_914_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
uint8_t v___y_908_; uint8_t v___x_912_; 
v___x_912_ = l_Lean_Exception_isInterrupt(v_a_900_);
if (v___x_912_ == 0)
{
uint8_t v___x_913_; 
lean_inc(v_a_900_);
v___x_913_ = l_Lean_Exception_isRuntime(v_a_900_);
v___y_908_ = v___x_913_;
goto v___jp_907_;
}
else
{
v___y_908_ = v___x_912_;
goto v___jp_907_;
}
v___jp_907_:
{
if (v___y_908_ == 0)
{
if (lean_obj_tag(v_a_900_) == 0)
{
lean_dec_ref_known(v_a_900_, 2);
lean_dec_ref_known(v___x_889_, 14);
lean_dec(v_stx_862_);
return v___x_906_;
}
else
{
lean_object* v_id_909_; uint8_t v___x_910_; 
v_id_909_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_id_909_);
lean_dec_ref_known(v_a_900_, 2);
v___x_910_ = l_Lean_instBEqInternalExceptionId_beq(v___x_904_, v_id_909_);
lean_dec(v_id_909_);
if (v___x_910_ == 0)
{
lean_dec_ref_known(v___x_889_, 14);
lean_dec(v_stx_862_);
return v___x_906_;
}
else
{
lean_object* v___x_911_; 
lean_dec_ref(v___x_906_);
v___x_911_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0(v_stx_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v___x_889_, v_a_868_);
lean_dec_ref_known(v___x_889_, 14);
return v___x_911_;
}
}
}
else
{
lean_dec(v_a_900_);
lean_dec_ref_known(v___x_889_, 14);
lean_dec(v_stx_862_);
return v___x_906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0___boxed(lean_object* v_stx_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(v_stx_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_924_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__1);
v___x_926_ = l_Lean_MessageData_ofExpr(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__0);
v___x_928_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__3);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_931_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__1);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(lean_object* v_stx_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_ty_x3f_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_fileName_947_; lean_object* v_fileMap_948_; lean_object* v_options_949_; lean_object* v_currRecDepth_950_; lean_object* v_maxRecDepth_951_; lean_object* v_ref_952_; lean_object* v_currNamespace_953_; lean_object* v_openDecls_954_; lean_object* v_initHeartbeats_955_; lean_object* v_maxHeartbeats_956_; lean_object* v_quotContext_957_; lean_object* v_currMacroScope_958_; uint8_t v_diag_959_; lean_object* v_cancelTk_x3f_960_; uint8_t v_suppressElabErrors_961_; lean_object* v_inheritedTraceOptions_962_; uint8_t v___x_963_; lean_object* v_ref_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_ty_x3f_941_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig___closed__2);
v___x_942_ = 1;
v___x_943_ = lean_box(0);
v___x_944_ = lean_box(v___x_942_);
v___x_945_ = lean_box(v___x_942_);
lean_inc(v_stx_933_);
v___x_946_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_946_, 0, v_stx_933_);
lean_closure_set(v___x_946_, 1, v_ty_x3f_941_);
lean_closure_set(v___x_946_, 2, v___x_944_);
lean_closure_set(v___x_946_, 3, v___x_945_);
lean_closure_set(v___x_946_, 4, v___x_943_);
v_fileName_947_ = lean_ctor_get(v_a_938_, 0);
v_fileMap_948_ = lean_ctor_get(v_a_938_, 1);
v_options_949_ = lean_ctor_get(v_a_938_, 2);
v_currRecDepth_950_ = lean_ctor_get(v_a_938_, 3);
v_maxRecDepth_951_ = lean_ctor_get(v_a_938_, 4);
v_ref_952_ = lean_ctor_get(v_a_938_, 5);
v_currNamespace_953_ = lean_ctor_get(v_a_938_, 6);
v_openDecls_954_ = lean_ctor_get(v_a_938_, 7);
v_initHeartbeats_955_ = lean_ctor_get(v_a_938_, 8);
v_maxHeartbeats_956_ = lean_ctor_get(v_a_938_, 9);
v_quotContext_957_ = lean_ctor_get(v_a_938_, 10);
v_currMacroScope_958_ = lean_ctor_get(v_a_938_, 11);
v_diag_959_ = lean_ctor_get_uint8(v_a_938_, sizeof(void*)*14);
v_cancelTk_x3f_960_ = lean_ctor_get(v_a_938_, 12);
v_suppressElabErrors_961_ = lean_ctor_get_uint8(v_a_938_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_962_ = lean_ctor_get(v_a_938_, 13);
v___x_963_ = 1;
v_ref_964_ = l_Lean_replaceRef(v_stx_933_, v_ref_952_);
lean_dec(v_stx_933_);
lean_inc_ref(v_inheritedTraceOptions_962_);
lean_inc(v_cancelTk_x3f_960_);
lean_inc(v_currMacroScope_958_);
lean_inc(v_quotContext_957_);
lean_inc(v_maxHeartbeats_956_);
lean_inc(v_initHeartbeats_955_);
lean_inc(v_openDecls_954_);
lean_inc(v_currNamespace_953_);
lean_inc(v_maxRecDepth_951_);
lean_inc(v_currRecDepth_950_);
lean_inc_ref(v_options_949_);
lean_inc_ref(v_fileMap_948_);
lean_inc_ref(v_fileName_947_);
v___x_965_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_965_, 0, v_fileName_947_);
lean_ctor_set(v___x_965_, 1, v_fileMap_948_);
lean_ctor_set(v___x_965_, 2, v_options_949_);
lean_ctor_set(v___x_965_, 3, v_currRecDepth_950_);
lean_ctor_set(v___x_965_, 4, v_maxRecDepth_951_);
lean_ctor_set(v___x_965_, 5, v_ref_964_);
lean_ctor_set(v___x_965_, 6, v_currNamespace_953_);
lean_ctor_set(v___x_965_, 7, v_openDecls_954_);
lean_ctor_set(v___x_965_, 8, v_initHeartbeats_955_);
lean_ctor_set(v___x_965_, 9, v_maxHeartbeats_956_);
lean_ctor_set(v___x_965_, 10, v_quotContext_957_);
lean_ctor_set(v___x_965_, 11, v_currMacroScope_958_);
lean_ctor_set(v___x_965_, 12, v_cancelTk_x3f_960_);
lean_ctor_set(v___x_965_, 13, v_inheritedTraceOptions_962_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*14, v_diag_959_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*14 + 1, v_suppressElabErrors_961_);
v___x_966_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_946_, v___x_963_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v___x_965_, v_a_939_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; uint8_t v___y_980_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; uint8_t v___x_1064_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_a_967_, v_a_937_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
v___x_1064_ = l_Lean_Expr_hasSorry(v_a_969_);
if (v___x_1064_ == 0)
{
v___y_1009_ = v_a_934_;
v___y_1010_ = v_a_935_;
v___y_1011_ = v_a_936_;
v___y_1012_ = v_a_937_;
v___y_1013_ = v___x_965_;
v___y_1014_ = v_a_939_;
goto v___jp_1008_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = l_Lean_Expr_hasSyntheticSorry(v_a_969_);
if (v___x_1065_ == 0)
{
v___y_1046_ = v_a_934_;
v___y_1047_ = v_a_935_;
v___y_1048_ = v_a_936_;
v___y_1049_ = v_a_937_;
v___y_1050_ = v___x_965_;
v___y_1051_ = v_a_939_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1066_; lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_969_);
lean_dec_ref_known(v___x_965_, 14);
v___x_1066_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
v___jp_970_:
{
if (v___y_980_ == 0)
{
if (lean_obj_tag(v___y_975_) == 0)
{
lean_dec_ref_known(v___y_975_, 2);
lean_dec_ref(v___y_973_);
lean_dec(v_a_969_);
return v___y_972_;
}
else
{
lean_object* v_id_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_994_; 
v_id_981_ = lean_ctor_get(v___y_975_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___y_975_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___y_975_, 1);
lean_dec(v_unused_995_);
v___x_983_ = v___y_975_;
v_isShared_984_ = v_isSharedCheck_994_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_id_981_);
lean_dec(v___y_975_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_994_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v___x_985_; 
v___x_985_ = l_Lean_instBEqInternalExceptionId_beq(v___y_971_, v_id_981_);
lean_dec(v_id_981_);
if (v___x_985_ == 0)
{
lean_del_object(v___x_983_);
lean_dec_ref(v___y_973_);
lean_dec(v_a_969_);
return v___y_972_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_dec_ref(v___y_972_);
v___x_986_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___closed__2);
v___x_987_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__1);
v___x_988_ = l_Lean_indentExpr(v_a_969_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 7);
lean_ctor_set(v___x_983_, 1, v___x_988_);
lean_ctor_set(v___x_983_, 0, v___x_987_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_986_);
v___x_992_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_991_, v___y_976_, v___y_979_, v___y_978_, v___y_974_, v___y_973_, v___y_977_);
lean_dec_ref(v___y_973_);
return v___x_992_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_975_);
lean_dec_ref(v___y_973_);
lean_dec(v_a_969_);
return v___y_972_;
}
}
v___jp_996_:
{
lean_object* v___x_1003_; 
lean_inc(v_a_969_);
v___x_1003_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr(v_a_969_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_dec_ref(v___y_1001_);
lean_dec(v_a_969_);
return v___x_1003_;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
v___x_1005_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1006_ = l_Lean_Exception_isInterrupt(v_a_1004_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
lean_inc(v_a_1004_);
v___x_1007_ = l_Lean_Exception_isRuntime(v_a_1004_);
v___y_971_ = v___x_1005_;
v___y_972_ = v___x_1003_;
v___y_973_ = v___y_1001_;
v___y_974_ = v___y_1000_;
v___y_975_ = v_a_1004_;
v___y_976_ = v___y_997_;
v___y_977_ = v___y_1002_;
v___y_978_ = v___y_999_;
v___y_979_ = v___y_998_;
v___y_980_ = v___x_1007_;
goto v___jp_970_;
}
else
{
v___y_971_ = v___x_1005_;
v___y_972_ = v___x_1003_;
v___y_973_ = v___y_1001_;
v___y_974_ = v___y_1000_;
v___y_975_ = v_a_1004_;
v___y_976_ = v___y_997_;
v___y_977_ = v___y_1002_;
v___y_978_ = v___y_999_;
v___y_979_ = v___y_998_;
v___y_980_ = v___x_1006_;
goto v___jp_970_;
}
}
}
v___jp_1008_:
{
lean_object* v___x_1015_; 
lean_inc(v_a_969_);
v___x_1015_ = l_Lean_Meta_getMVars(v_a_969_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1016_, v___x_943_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v_a_1016_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; uint8_t v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = lean_unbox(v_a_1018_);
lean_dec(v_a_1018_);
if (v___x_1019_ == 0)
{
v___y_997_ = v___y_1009_;
v___y_998_ = v___y_1010_;
v___y_999_ = v___y_1011_;
v___y_1000_ = v___y_1012_;
v___y_1001_ = v___y_1013_;
v___y_1002_ = v___y_1014_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v___y_1013_);
lean_dec(v_a_969_);
v___x_1020_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v___y_1013_);
lean_dec(v_a_969_);
v_a_1029_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1017_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1017_);
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
lean_dec_ref(v___y_1013_);
lean_dec(v_a_969_);
v_a_1037_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1015_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1015_);
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
v___jp_1045_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v___x_1052_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__9);
v___x_1053_ = l_Lean_indentExpr(v_a_969_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v___x_1054_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec_ref(v___y_1050_);
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref_known(v___x_965_, 14);
v_a_1075_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_966_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_966_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1___boxed(lean_object* v_stx_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(v_stx_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(lean_object* v_config_1167_, lean_object* v_item_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_item_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_1187_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(v_item_1168_, v___x_1186_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1187_) == 0)
{
uint8_t v___x_1188_; 
lean_dec_ref_known(v___x_1187_, 1);
v___x_1188_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_1168_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1189_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_1168_);
lean_inc_ref(v_item_1168_);
v___x_1190_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_1168_);
v___x_1191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__1));
v___x_1192_ = lean_string_dec_lt(v___x_1189_, v___x_1191_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_string_dec_eq(v___x_1189_, v___x_1191_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__2));
v___x_1195_ = lean_string_dec_eq(v___x_1189_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__3));
v___x_1197_ = lean_string_dec_eq(v___x_1189_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__4));
v___x_1199_ = lean_string_dec_eq(v___x_1189_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__5));
v___x_1201_ = lean_string_dec_eq(v___x_1189_, v___x_1200_);
lean_dec_ref(v___x_1189_);
if (v___x_1201_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__6));
v___x_1203_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1202_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1203_) == 0)
{
uint8_t v___x_1204_; 
lean_dec_ref_known(v___x_1203_, 1);
v___x_1204_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1204_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1205_; 
lean_dec_ref(v___x_1190_);
v___x_1205_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1228_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1228_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
uint8_t v_leave_1210_; uint8_t v_elimLets_1211_; uint8_t v_jp_1212_; lean_object* v_stepLimit_1213_; uint8_t v_errorOnMissingSpec_1214_; uint8_t v_debug_1215_; uint8_t v_internalize_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1227_; 
v_leave_1210_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 1);
v_elimLets_1211_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 2);
v_jp_1212_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 3);
v_stepLimit_1213_ = lean_ctor_get(v_config_1167_, 0);
v_errorOnMissingSpec_1214_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 4);
v_debug_1215_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 5);
v_internalize_1216_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 6);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1218_ = v_config_1167_;
v_isShared_1219_ = v_isSharedCheck_1227_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_stepLimit_1213_);
lean_dec(v_config_1167_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1227_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_stepLimit_1213_);
v___x_1221_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
uint8_t v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_unbox(v_a_1206_);
lean_dec(v_a_1206_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1, v___x_1222_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1 + 1, v_leave_1210_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1 + 2, v_elimLets_1211_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1 + 3, v_jp_1212_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1214_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1 + 5, v_debug_1215_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1 + 6, v_internalize_1216_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1221_);
v___x_1224_ = v___x_1208_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1221_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v_config_1167_);
v_a_1229_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1205_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1205_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1237_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1203_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1203_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v___x_1189_);
v___x_1245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__7));
v___x_1246_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1245_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1246_) == 0)
{
uint8_t v___x_1247_; 
lean_dec_ref_known(v___x_1246_, 1);
v___x_1247_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1247_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1248_; 
lean_dec_ref(v___x_1190_);
lean_inc_ref(v_item_1168_);
v___x_1248_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_value_1249_; lean_object* v___x_1250_; 
lean_dec_ref_known(v___x_1248_, 1);
v_value_1249_ = lean_ctor_get(v_item_1168_, 2);
lean_inc(v_value_1249_);
lean_dec_ref(v_item_1168_);
v___x_1250_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0(v_value_1249_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1273_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1273_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
uint8_t v_trivial_1255_; uint8_t v_leave_1256_; uint8_t v_elimLets_1257_; uint8_t v_jp_1258_; uint8_t v_errorOnMissingSpec_1259_; uint8_t v_debug_1260_; uint8_t v_internalize_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1271_; 
v_trivial_1255_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1);
v_leave_1256_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 1);
v_elimLets_1257_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 2);
v_jp_1258_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 3);
v_errorOnMissingSpec_1259_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 4);
v_debug_1260_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 5);
v_internalize_1261_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 6);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_config_1167_, 0);
lean_dec(v_unused_1272_);
v___x_1263_ = v_config_1167_;
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v_config_1167_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_a_1251_);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*1, v_trivial_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*1 + 1, v_leave_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*1 + 2, v_elimLets_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*1 + 3, v_jp_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*1 + 5, v_debug_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*1 + 6, v_internalize_1261_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1266_);
v___x_1268_ = v___x_1253_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v_config_1167_);
v_a_1274_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1250_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1250_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1282_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1248_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1248_);
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
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1290_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1246_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1246_);
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
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v___x_1189_);
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__8));
v___x_1299_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1298_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1299_) == 0)
{
uint8_t v___x_1300_; 
lean_dec_ref_known(v___x_1299_, 1);
v___x_1300_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1300_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1301_; 
lean_dec_ref(v___x_1190_);
v___x_1301_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1324_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1324_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1324_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
uint8_t v_trivial_1306_; uint8_t v_elimLets_1307_; uint8_t v_jp_1308_; lean_object* v_stepLimit_1309_; uint8_t v_errorOnMissingSpec_1310_; uint8_t v_debug_1311_; uint8_t v_internalize_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1323_; 
v_trivial_1306_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1);
v_elimLets_1307_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 2);
v_jp_1308_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 3);
v_stepLimit_1309_ = lean_ctor_get(v_config_1167_, 0);
v_errorOnMissingSpec_1310_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 4);
v_debug_1311_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 5);
v_internalize_1312_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 6);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1314_ = v_config_1167_;
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_stepLimit_1309_);
lean_dec(v_config_1167_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_stepLimit_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*1, v_trivial_1306_);
v___x_1317_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
uint8_t v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = lean_unbox(v_a_1302_);
lean_dec(v_a_1302_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*1 + 1, v___x_1318_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*1 + 2, v_elimLets_1307_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*1 + 3, v_jp_1308_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1310_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*1 + 5, v_debug_1311_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*1 + 6, v_internalize_1312_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1317_);
v___x_1320_ = v___x_1304_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1317_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_config_1167_);
v_a_1325_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1301_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1301_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1333_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1299_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1299_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v___x_1189_);
v___x_1341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__9));
v___x_1342_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1341_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1342_) == 0)
{
uint8_t v___x_1343_; 
lean_dec_ref_known(v___x_1342_, 1);
v___x_1343_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1190_);
v___x_1344_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1367_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1367_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1367_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v_trivial_1349_; uint8_t v_leave_1350_; uint8_t v_elimLets_1351_; lean_object* v_stepLimit_1352_; uint8_t v_errorOnMissingSpec_1353_; uint8_t v_debug_1354_; uint8_t v_internalize_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1366_; 
v_trivial_1349_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1);
v_leave_1350_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 1);
v_elimLets_1351_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 2);
v_stepLimit_1352_ = lean_ctor_get(v_config_1167_, 0);
v_errorOnMissingSpec_1353_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 4);
v_debug_1354_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 5);
v_internalize_1355_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 6);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1357_ = v_config_1167_;
v_isShared_1358_ = v_isSharedCheck_1366_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_stepLimit_1352_);
lean_dec(v_config_1167_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1366_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_stepLimit_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*1, v_trivial_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*1 + 1, v_leave_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*1 + 2, v_elimLets_1351_);
v___x_1360_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
uint8_t v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1 + 3, v___x_1361_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1353_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1 + 5, v_debug_1354_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1 + 6, v_internalize_1355_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1360_);
v___x_1363_ = v___x_1347_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1360_);
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
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v_config_1167_);
v_a_1368_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1344_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1344_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1376_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1342_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1342_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v___x_1189_);
v___x_1384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__10));
v___x_1385_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1384_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1385_) == 0)
{
uint8_t v___x_1386_; 
lean_dec_ref_known(v___x_1385_, 1);
v___x_1386_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1386_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1387_; 
lean_dec_ref(v___x_1190_);
v___x_1387_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1410_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1410_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1410_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
uint8_t v_trivial_1392_; uint8_t v_leave_1393_; uint8_t v_elimLets_1394_; uint8_t v_jp_1395_; lean_object* v_stepLimit_1396_; uint8_t v_errorOnMissingSpec_1397_; uint8_t v_debug_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1409_; 
v_trivial_1392_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1);
v_leave_1393_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 1);
v_elimLets_1394_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 2);
v_jp_1395_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 3);
v_stepLimit_1396_ = lean_ctor_get(v_config_1167_, 0);
v_errorOnMissingSpec_1397_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 4);
v_debug_1398_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 5);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1400_ = v_config_1167_;
v_isShared_1401_ = v_isSharedCheck_1409_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_stepLimit_1396_);
lean_dec(v_config_1167_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1409_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_stepLimit_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*1, v_trivial_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*1 + 1, v_leave_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*1 + 2, v_elimLets_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*1 + 3, v_jp_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*1 + 5, v_debug_1398_);
v___x_1403_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
uint8_t v___x_1404_; lean_object* v___x_1406_; 
v___x_1404_ = lean_unbox(v_a_1388_);
lean_dec(v_a_1388_);
lean_ctor_set_uint8(v___x_1403_, sizeof(void*)*1 + 6, v___x_1404_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1403_);
v___x_1406_ = v___x_1390_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1403_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v_config_1167_);
v_a_1411_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1387_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1387_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1419_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1385_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1385_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__11));
v___x_1428_ = lean_string_dec_eq(v___x_1189_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__12));
v___x_1430_ = lean_string_dec_eq(v___x_1189_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__13));
v___x_1432_ = lean_string_dec_eq(v___x_1189_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__14));
v___x_1434_ = lean_string_dec_eq(v___x_1189_, v___x_1433_);
lean_dec_ref(v___x_1189_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__15));
v___x_1436_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1435_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1436_) == 0)
{
uint8_t v___x_1437_; 
lean_dec_ref_known(v___x_1436_, 1);
v___x_1437_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1437_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1438_; 
lean_dec_ref(v___x_1190_);
v___x_1438_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1461_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1461_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1461_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
uint8_t v_trivial_1443_; uint8_t v_leave_1444_; uint8_t v_elimLets_1445_; uint8_t v_jp_1446_; lean_object* v_stepLimit_1447_; uint8_t v_debug_1448_; uint8_t v_internalize_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v_trivial_1443_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1);
v_leave_1444_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 1);
v_elimLets_1445_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 2);
v_jp_1446_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 3);
v_stepLimit_1447_ = lean_ctor_get(v_config_1167_, 0);
v_debug_1448_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 5);
v_internalize_1449_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 6);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v_config_1167_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_stepLimit_1447_);
lean_dec(v_config_1167_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
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
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_stepLimit_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*1, v_trivial_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*1 + 1, v_leave_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*1 + 2, v_elimLets_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*1 + 3, v_jp_1446_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
uint8_t v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_unbox(v_a_1439_);
lean_dec(v_a_1439_);
lean_ctor_set_uint8(v___x_1454_, sizeof(void*)*1 + 4, v___x_1455_);
lean_ctor_set_uint8(v___x_1454_, sizeof(void*)*1 + 5, v_debug_1448_);
lean_ctor_set_uint8(v___x_1454_, sizeof(void*)*1 + 6, v_internalize_1449_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1454_);
v___x_1457_ = v___x_1441_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1454_);
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
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_config_1167_);
v_a_1462_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1438_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1438_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1470_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1436_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1436_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v___x_1189_);
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__16));
v___x_1479_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1478_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1479_) == 0)
{
uint8_t v___x_1480_; 
lean_dec_ref_known(v___x_1479_, 1);
v___x_1480_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1480_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1481_; 
lean_dec_ref(v___x_1190_);
v___x_1481_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1504_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1504_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1504_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint8_t v_trivial_1486_; uint8_t v_leave_1487_; uint8_t v_jp_1488_; lean_object* v_stepLimit_1489_; uint8_t v_errorOnMissingSpec_1490_; uint8_t v_debug_1491_; uint8_t v_internalize_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1503_; 
v_trivial_1486_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1);
v_leave_1487_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 1);
v_jp_1488_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 3);
v_stepLimit_1489_ = lean_ctor_get(v_config_1167_, 0);
v_errorOnMissingSpec_1490_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 4);
v_debug_1491_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 5);
v_internalize_1492_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 6);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1494_ = v_config_1167_;
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_stepLimit_1489_);
lean_dec(v_config_1167_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_stepLimit_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*1, v_trivial_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1502_, sizeof(void*)*1 + 1, v_leave_1487_);
v___x_1497_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
uint8_t v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_unbox(v_a_1482_);
lean_dec(v_a_1482_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*1 + 2, v___x_1498_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*1 + 3, v_jp_1488_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1490_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*1 + 5, v_debug_1491_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*1 + 6, v_internalize_1492_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1497_);
v___x_1500_ = v___x_1484_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1497_);
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
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v_config_1167_);
v_a_1505_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1481_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1481_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1513_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1479_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1479_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v___x_1189_);
v___x_1521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__17));
v___x_1522_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(v_item_1168_, v___x_1521_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1522_) == 0)
{
uint8_t v___x_1523_; 
lean_dec_ref_known(v___x_1522_, 1);
v___x_1523_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1523_ == 0)
{
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1524_; 
lean_dec_ref(v___x_1190_);
v___x_1524_ = l_Lean_Elab_ConfigEval_evalBoolItem(v_item_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1547_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v_trivial_1529_; uint8_t v_leave_1530_; uint8_t v_elimLets_1531_; uint8_t v_jp_1532_; lean_object* v_stepLimit_1533_; uint8_t v_errorOnMissingSpec_1534_; uint8_t v_internalize_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1546_; 
v_trivial_1529_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1);
v_leave_1530_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 1);
v_elimLets_1531_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 2);
v_jp_1532_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 3);
v_stepLimit_1533_ = lean_ctor_get(v_config_1167_, 0);
v_errorOnMissingSpec_1534_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 4);
v_internalize_1535_ = lean_ctor_get_uint8(v_config_1167_, sizeof(void*)*1 + 6);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_config_1167_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1537_ = v_config_1167_;
v_isShared_1538_ = v_isSharedCheck_1546_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_stepLimit_1533_);
lean_dec(v_config_1167_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1546_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_stepLimit_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*1, v_trivial_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*1 + 1, v_leave_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*1 + 2, v_elimLets_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*1 + 3, v_jp_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*1 + 4, v_errorOnMissingSpec_1534_);
v___x_1540_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
uint8_t v___x_1541_; lean_object* v___x_1543_; 
v___x_1541_ = lean_unbox(v_a_1525_);
lean_dec(v_a_1525_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*1 + 5, v___x_1541_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*1 + 6, v_internalize_1535_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1540_);
v___x_1543_ = v___x_1527_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1540_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref(v_config_1167_);
v_a_1548_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1524_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1524_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v___x_1190_);
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1556_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1522_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1522_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
else
{
uint8_t v___x_1564_; 
lean_dec_ref(v___x_1189_);
lean_dec_ref(v_config_1167_);
v___x_1564_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_1190_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v_item_1168_);
v_item_1177_ = v___x_1190_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
else
{
lean_object* v_value_1565_; lean_object* v___x_1566_; 
lean_dec_ref(v___x_1190_);
v_value_1565_ = lean_ctor_get(v_item_1168_, 2);
lean_inc(v_value_1565_);
lean_dec_ref(v_item_1168_);
v___x_1566_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1(v_value_1565_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1566_;
}
}
}
}
else
{
lean_dec_ref(v_config_1167_);
v_item_1177_ = v_item_1168_;
v___y_1178_ = v___y_1169_;
v___y_1179_ = v___y_1170_;
v___y_1180_ = v___y_1171_;
v___y_1181_ = v___y_1172_;
v___y_1182_ = v___y_1173_;
v___y_1183_ = v___y_1174_;
goto v___jp_1176_;
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec_ref(v_item_1168_);
lean_dec_ref(v_config_1167_);
v_a_1567_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1187_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1187_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
v___jp_1176_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___closed__0));
v___x_1185_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(v_item_1177_, v___x_1184_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0___boxed(lean_object* v_config_1575_, lean_object* v_item_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___lam__0(v_config_1575_, v_item_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(lean_object* v_e_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___redArg(v_e_1587_, v___y_1591_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2___boxed(lean_object* v_e_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__2(v_e_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4(lean_object* v_00_u03b1_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__4___redArg();
return v___x_1613_;
}
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(lean_object* v_00_u03b1_1623_, lean_object* v_msg_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___redArg(v_msg_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1633_, lean_object* v_msg_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3(v_00_u03b1_1633_, v_msg_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(lean_object* v_msgData_1643_, lean_object* v_macroStack_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___redArg(v_msgData_1643_, v_macroStack_1644_, v___y_1649_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4___boxed(lean_object* v_msgData_1653_, lean_object* v_macroStack_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__1_spec__3_spec__4(v_msgData_1653_, v_macroStack_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
return v_res_1662_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_box(0);
v___x_1664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr___closed__3));
v___x_1665_ = l_Lean_mkConst(v___x_1664_, v___x_1663_);
return v___x_1665_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__0);
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(lean_object* v_cfg_1668_, lean_object* v_cfgItem_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___closed__1);
v___x_1678_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(v_cfg_1668_, v_cfgItem_1669_, v___x_1677_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0___boxed(lean_object* v_cfg_1679_, lean_object* v_cfgItem_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg___lam__0(v_cfg_1679_, v_cfgItem_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_cfgItem_1680_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg(lean_object* v_cfg_1690_, lean_object* v_init_1691_, uint8_t v_logExceptions_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_onErr_1697_; lean_object* v_eval_1698_; 
v_onErr_1697_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elabConfig___redArg___closed__0));
v_eval_1698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem___closed__0));
if (v_logExceptions_1692_ == 0)
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1698_, v_init_1691_, v_cfg_1690_, v_onErr_1697_, v_logExceptions_1692_, v_a_1694_, v_a_1695_);
return v___x_1699_;
}
else
{
uint8_t v_recover_1700_; lean_object* v___x_1701_; 
v_recover_1700_ = lean_ctor_get_uint8(v_a_1693_, sizeof(void*)*1);
v___x_1701_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(v_eval_1698_, v_init_1691_, v_cfg_1690_, v_onErr_1697_, v_recover_1700_, v_a_1694_, v_a_1695_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___redArg___boxed(lean_object* v_cfg_1702_, lean_object* v_init_1703_, lean_object* v_logExceptions_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
uint8_t v_logExceptions_boxed_1709_; lean_object* v_res_1710_; 
v_logExceptions_boxed_1709_ = lean_unbox(v_logExceptions_1704_);
v_res_1710_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_cfg_1702_, v_init_1703_, v_logExceptions_boxed_1709_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec_ref(v_a_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig(lean_object* v_cfg_1711_, lean_object* v_init_1712_, uint8_t v_logExceptions_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_cfg_1711_, v_init_1712_, v_logExceptions_1713_, v_a_1714_, v_a_1720_, v_a_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object* v_cfg_1724_, lean_object* v_init_1725_, lean_object* v_logExceptions_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
uint8_t v_logExceptions_boxed_1736_; lean_object* v_res_1737_; 
v_logExceptions_boxed_1736_ = lean_unbox(v_logExceptions_1726_);
v_res_1737_ = l_Lean_Elab_Tactic_Do_elabConfig(v_cfg_1724_, v_init_1725_, v_logExceptions_boxed_1736_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg(lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1743_; lean_object* v_fuel_1744_; 
v___x_1743_ = lean_st_ref_get(v_a_1738_);
v_fuel_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_fuel_1744_);
if (lean_obj_tag(v_fuel_1744_) == 0)
{
lean_object* v_simpState_1745_; lean_object* v_invariants_1746_; lean_object* v_vcs_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1769_; 
v_simpState_1745_ = lean_ctor_get(v___x_1743_, 1);
v_invariants_1746_ = lean_ctor_get(v___x_1743_, 2);
v_vcs_1747_ = lean_ctor_get(v___x_1743_, 3);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1743_, 0);
lean_dec(v_unused_1770_);
v___x_1749_ = v___x_1743_;
v_isShared_1750_ = v_isSharedCheck_1769_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_vcs_1747_);
lean_inc(v_invariants_1746_);
lean_inc(v_simpState_1745_);
lean_dec(v___x_1743_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1769_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_n_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1768_; 
v_n_1751_ = lean_ctor_get(v_fuel_1744_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_fuel_1744_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1753_ = v_fuel_1744_;
v_isShared_1754_ = v_isSharedCheck_1768_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_n_1751_);
lean_dec(v_fuel_1744_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1768_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_zero_1755_; uint8_t v_isZero_1756_; 
v_zero_1755_ = lean_unsigned_to_nat(0u);
v_isZero_1756_ = lean_nat_dec_eq(v_n_1751_, v_zero_1755_);
if (v_isZero_1756_ == 1)
{
lean_del_object(v___x_1753_);
lean_dec(v_n_1751_);
lean_del_object(v___x_1749_);
lean_dec_ref(v_vcs_1747_);
lean_dec_ref(v_invariants_1746_);
lean_dec_ref(v_simpState_1745_);
goto v___jp_1740_;
}
else
{
lean_object* v_one_1757_; lean_object* v_n_1758_; lean_object* v___x_1760_; 
v_one_1757_ = lean_unsigned_to_nat(1u);
v_n_1758_ = lean_nat_sub(v_n_1751_, v_one_1757_);
lean_dec(v_n_1751_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v_n_1758_);
v___x_1760_ = v___x_1753_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_n_1758_);
v___x_1760_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1762_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1760_);
v___x_1762_ = v___x_1749_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_simpState_1745_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_invariants_1746_);
lean_ctor_set(v_reuseFailAlloc_1766_, 3, v_vcs_1747_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_st_ref_swap(v_a_1738_, v___x_1762_);
lean_dec(v___x_1763_);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1743_);
goto v___jp_1740_;
}
v___jp_1740_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___redArg___boxed(lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1771_);
lean_dec(v_a_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne(lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Elab_Tactic_Do_burnOne___redArg(v_a_1775_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_burnOne___boxed(lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Elab_Tactic_Do_burnOne(v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(lean_object* v_x_1790_, lean_object* v_k_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v_fuel_1800_; 
v___x_1799_ = lean_st_ref_get(v_a_1793_);
v_fuel_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_fuel_1800_);
lean_dec(v___x_1799_);
if (lean_obj_tag(v_fuel_1800_) == 0)
{
lean_object* v_n_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_n_1801_ = lean_ctor_get(v_fuel_1800_, 0);
lean_inc(v_n_1801_);
lean_dec_ref_known(v_fuel_1800_, 1);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_nat_dec_eq(v_n_1801_, v___x_1802_);
lean_dec(v_n_1801_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v_x_1790_);
lean_inc(v_a_1797_);
lean_inc_ref(v_a_1796_);
lean_inc(v_a_1795_);
lean_inc_ref(v_a_1794_);
lean_inc(v_a_1793_);
lean_inc_ref(v_a_1792_);
v___x_1804_ = lean_apply_7(v_k_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, lean_box(0));
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; 
lean_dec_ref(v_k_1791_);
lean_inc(v_a_1797_);
lean_inc_ref(v_a_1796_);
lean_inc(v_a_1795_);
lean_inc_ref(v_a_1794_);
lean_inc(v_a_1793_);
lean_inc_ref(v_a_1792_);
v___x_1805_ = lean_apply_7(v_x_1790_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, lean_box(0));
return v___x_1805_;
}
}
else
{
lean_object* v___x_1806_; 
lean_dec(v_fuel_1800_);
lean_dec_ref(v_x_1790_);
lean_inc(v_a_1797_);
lean_inc_ref(v_a_1796_);
lean_inc(v_a_1795_);
lean_inc_ref(v_a_1794_);
lean_inc(v_a_1793_);
lean_inc_ref(v_a_1792_);
v___x_1806_ = lean_apply_7(v_k_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, lean_box(0));
return v___x_1806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg___boxed(lean_object* v_x_1807_, lean_object* v_k_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1807_, v_k_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel(lean_object* v_00_u03b1_1817_, lean_object* v_x_1818_, lean_object* v_k_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel___redArg(v_x_1818_, v_k_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ifOutOfFuel___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_x_1829_, lean_object* v_k_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Elab_Tactic_Do_ifOutOfFuel(v_00_u03b1_1828_, v_x_1829_, v_k_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v_ks_1843_; lean_object* v_vs_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1868_; 
v_ks_1843_ = lean_ctor_get(v_x_1839_, 0);
v_vs_1844_ = lean_ctor_get(v_x_1839_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_x_1839_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1846_ = v_x_1839_;
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_vs_1844_);
lean_inc(v_ks_1843_);
lean_dec(v_x_1839_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = lean_array_get_size(v_ks_1843_);
v___x_1849_ = lean_nat_dec_lt(v_x_1840_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec(v_x_1840_);
v___x_1850_ = lean_array_push(v_ks_1843_, v_x_1841_);
v___x_1851_ = lean_array_push(v_vs_1844_, v_x_1842_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1851_);
lean_ctor_set(v___x_1846_, 0, v___x_1850_);
v___x_1853_ = v___x_1846_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v_k_x27_1855_; uint8_t v___x_1856_; 
v_k_x27_1855_ = lean_array_fget_borrowed(v_ks_1843_, v_x_1840_);
v___x_1856_ = l_Lean_instBEqMVarId_beq(v_x_1841_, v_k_x27_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1858_; 
if (v_isShared_1847_ == 0)
{
v___x_1858_ = v___x_1846_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_ks_1843_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_vs_1844_);
v___x_1858_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_nat_add(v_x_1840_, v___x_1859_);
lean_dec(v_x_1840_);
v_x_1839_ = v___x_1858_;
v_x_1840_ = v___x_1860_;
goto _start;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = lean_array_fset(v_ks_1843_, v_x_1840_, v_x_1841_);
v___x_1864_ = lean_array_fset(v_vs_1844_, v_x_1840_, v_x_1842_);
lean_dec(v_x_1840_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1864_);
lean_ctor_set(v___x_1846_, 0, v___x_1863_);
v___x_1866_ = v___x_1846_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1864_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_n_1869_, lean_object* v_k_1870_, lean_object* v_v_1871_){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_n_1869_, v___x_1872_, v_k_1870_, v_v_1871_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1875_, size_t v_x_1876_, size_t v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v_es_1880_; size_t v___x_1881_; size_t v___x_1882_; lean_object* v_j_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_es_1880_ = lean_ctor_get(v_x_1875_, 0);
v___x_1881_ = ((size_t)31ULL);
v___x_1882_ = lean_usize_land(v_x_1876_, v___x_1881_);
v_j_1883_ = lean_usize_to_nat(v___x_1882_);
v___x_1884_ = lean_array_get_size(v_es_1880_);
v___x_1885_ = lean_nat_dec_lt(v_j_1883_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_dec(v_j_1883_);
lean_dec(v_x_1879_);
lean_dec(v_x_1878_);
return v_x_1875_;
}
else
{
lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1924_; 
lean_inc_ref(v_es_1880_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v_x_1875_, 0);
lean_dec(v_unused_1925_);
v___x_1887_ = v_x_1875_;
v_isShared_1888_ = v_isSharedCheck_1924_;
goto v_resetjp_1886_;
}
else
{
lean_dec(v_x_1875_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1924_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_v_1889_; lean_object* v___x_1890_; lean_object* v_xs_x27_1891_; lean_object* v___y_1893_; 
v_v_1889_ = lean_array_fget(v_es_1880_, v_j_1883_);
v___x_1890_ = lean_box(0);
v_xs_x27_1891_ = lean_array_fset(v_es_1880_, v_j_1883_, v___x_1890_);
switch(lean_obj_tag(v_v_1889_))
{
case 0:
{
lean_object* v_key_1898_; lean_object* v_val_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1909_; 
v_key_1898_ = lean_ctor_get(v_v_1889_, 0);
v_val_1899_ = lean_ctor_get(v_v_1889_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_v_1889_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1901_ = v_v_1889_;
v_isShared_1902_ = v_isSharedCheck_1909_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_val_1899_);
lean_inc(v_key_1898_);
lean_dec(v_v_1889_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1909_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
uint8_t v___x_1903_; 
v___x_1903_ = l_Lean_instBEqMVarId_beq(v_x_1878_, v_key_1898_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_del_object(v___x_1901_);
v___x_1904_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1898_, v_val_1899_, v_x_1878_, v_x_1879_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
v___y_1893_ = v___x_1905_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1907_; 
lean_dec(v_val_1899_);
lean_dec(v_key_1898_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v_x_1879_);
lean_ctor_set(v___x_1901_, 0, v_x_1878_);
v___x_1907_ = v___x_1901_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_x_1878_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_x_1879_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1893_ = v___x_1907_;
goto v___jp_1892_;
}
}
}
}
case 1:
{
lean_object* v_node_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1922_; 
v_node_1910_ = lean_ctor_get(v_v_1889_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_v_1889_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1912_ = v_v_1889_;
v_isShared_1913_ = v_isSharedCheck_1922_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_node_1910_);
lean_dec(v_v_1889_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1922_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
size_t v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1914_ = ((size_t)5ULL);
v___x_1915_ = lean_usize_shift_right(v_x_1876_, v___x_1914_);
v___x_1916_ = ((size_t)1ULL);
v___x_1917_ = lean_usize_add(v_x_1877_, v___x_1916_);
v___x_1918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_node_1910_, v___x_1915_, v___x_1917_, v_x_1878_, v_x_1879_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1918_);
v___x_1920_ = v___x_1912_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1893_ = v___x_1920_;
goto v___jp_1892_;
}
}
}
default: 
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_x_1878_);
lean_ctor_set(v___x_1923_, 1, v_x_1879_);
v___y_1893_ = v___x_1923_;
goto v___jp_1892_;
}
}
v___jp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_array_fset(v_xs_x27_1891_, v_j_1883_, v___y_1893_);
lean_dec(v_j_1883_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1894_);
v___x_1896_ = v___x_1887_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
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
}
else
{
lean_object* v_ks_1926_; lean_object* v_vs_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1945_; 
v_ks_1926_ = lean_ctor_get(v_x_1875_, 0);
v_vs_1927_ = lean_ctor_get(v_x_1875_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1929_ = v_x_1875_;
v_isShared_1930_ = v_isSharedCheck_1945_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_vs_1927_);
lean_inc(v_ks_1926_);
lean_dec(v_x_1875_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1945_;
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
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_ks_1926_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_vs_1927_);
v___x_1932_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v_newNode_1933_; size_t v___x_1934_; uint8_t v___x_1935_; 
v_newNode_1933_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v___x_1932_, v_x_1878_, v_x_1879_);
v___x_1934_ = ((size_t)7ULL);
v___x_1935_ = lean_usize_dec_le(v___x_1934_, v_x_1877_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1936_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1933_);
v___x_1937_ = lean_unsigned_to_nat(4u);
v___x_1938_ = lean_nat_dec_lt(v___x_1936_, v___x_1937_);
lean_dec(v___x_1936_);
if (v___x_1938_ == 0)
{
lean_object* v_ks_1939_; lean_object* v_vs_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_ks_1939_ = lean_ctor_get(v_newNode_1933_, 0);
lean_inc_ref(v_ks_1939_);
v_vs_1940_ = lean_ctor_get(v_newNode_1933_, 1);
lean_inc_ref(v_vs_1940_);
lean_dec_ref(v_newNode_1933_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_x_1877_, v_ks_1939_, v_vs_1940_, v___x_1941_, v___x_1942_);
lean_dec_ref(v_vs_1940_);
lean_dec_ref(v_ks_1939_);
return v___x_1943_;
}
else
{
return v_newNode_1933_;
}
}
else
{
return v_newNode_1933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(size_t v_depth_1946_, lean_object* v_keys_1947_, lean_object* v_vals_1948_, lean_object* v_i_1949_, lean_object* v_entries_1950_){
_start:
{
lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1951_ = lean_array_get_size(v_keys_1947_);
v___x_1952_ = lean_nat_dec_lt(v_i_1949_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_dec(v_i_1949_);
return v_entries_1950_;
}
else
{
lean_object* v_k_1953_; lean_object* v_v_1954_; uint64_t v___x_1955_; size_t v_h_1956_; size_t v___x_1957_; lean_object* v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; size_t v___x_1961_; size_t v_h_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_k_1953_ = lean_array_fget_borrowed(v_keys_1947_, v_i_1949_);
v_v_1954_ = lean_array_fget_borrowed(v_vals_1948_, v_i_1949_);
v___x_1955_ = l_Lean_instHashableMVarId_hash(v_k_1953_);
v_h_1956_ = lean_uint64_to_usize(v___x_1955_);
v___x_1957_ = ((size_t)5ULL);
v___x_1958_ = lean_unsigned_to_nat(1u);
v___x_1959_ = ((size_t)1ULL);
v___x_1960_ = lean_usize_sub(v_depth_1946_, v___x_1959_);
v___x_1961_ = lean_usize_mul(v___x_1957_, v___x_1960_);
v_h_1962_ = lean_usize_shift_right(v_h_1956_, v___x_1961_);
v___x_1963_ = lean_nat_add(v_i_1949_, v___x_1958_);
lean_dec(v_i_1949_);
lean_inc(v_v_1954_);
lean_inc(v_k_1953_);
v___x_1964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_entries_1950_, v_h_1962_, v_depth_1946_, v_k_1953_, v_v_1954_);
v_i_1949_ = v___x_1963_;
v_entries_1950_ = v___x_1964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_depth_1966_, lean_object* v_keys_1967_, lean_object* v_vals_1968_, lean_object* v_i_1969_, lean_object* v_entries_1970_){
_start:
{
size_t v_depth_boxed_1971_; lean_object* v_res_1972_; 
v_depth_boxed_1971_ = lean_unbox_usize(v_depth_1966_);
lean_dec(v_depth_1966_);
v_res_1972_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_boxed_1971_, v_keys_1967_, v_vals_1968_, v_i_1969_, v_entries_1970_);
lean_dec_ref(v_vals_1968_);
lean_dec_ref(v_keys_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_){
_start:
{
size_t v_x_7158__boxed_1978_; size_t v_x_7159__boxed_1979_; lean_object* v_res_1980_; 
v_x_7158__boxed_1978_ = lean_unbox_usize(v_x_1974_);
lean_dec(v_x_1974_);
v_x_7159__boxed_1979_ = lean_unbox_usize(v_x_1975_);
lean_dec(v_x_1975_);
v_res_1980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1973_, v_x_7158__boxed_1978_, v_x_7159__boxed_1979_, v_x_1976_, v_x_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
uint64_t v___x_1984_; size_t v___x_1985_; size_t v___x_1986_; lean_object* v___x_1987_; 
v___x_1984_ = l_Lean_instHashableMVarId_hash(v_x_1982_);
v___x_1985_ = lean_uint64_to_usize(v___x_1984_);
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_1981_, v___x_1985_, v___x_1986_, v_x_1982_, v_x_1983_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(lean_object* v_range_1988_, lean_object* v_b_1989_, lean_object* v_i_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_stop_1994_; lean_object* v_step_1995_; lean_object* v_a_1997_; lean_object* v___y_2001_; uint8_t v___x_2017_; 
v_stop_1994_ = lean_ctor_get(v_range_1988_, 1);
v_step_1995_ = lean_ctor_get(v_range_1988_, 2);
v___x_2017_ = lean_nat_dec_lt(v_i_1990_, v_stop_1994_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec(v_i_1990_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_b_1989_);
return v___x_2018_;
}
else
{
lean_object* v_decls_2019_; lean_object* v_size_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_decls_2019_ = lean_ctor_get(v_b_1989_, 1);
v_size_2020_ = lean_ctor_get(v_decls_2019_, 2);
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_nat_dec_lt(v_i_1990_, v_size_2020_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = l_outOfBounds___redArg(v___x_2021_);
v___y_2001_ = v___x_2023_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2021_, v_decls_2019_, v_i_1990_);
v___y_2001_ = v___x_2024_;
goto v___jp_2000_;
}
}
v___jp_1996_:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_nat_add(v_i_1990_, v_step_1995_);
lean_dec(v_i_1990_);
v_b_1989_ = v_a_1997_;
v_i_1990_ = v___x_1998_;
goto _start;
}
v___jp_2000_:
{
if (lean_obj_tag(v___y_2001_) == 1)
{
lean_object* v_val_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v_val_2002_ = lean_ctor_get(v___y_2001_, 0);
lean_inc(v_val_2002_);
lean_dec_ref_known(v___y_2001_, 1);
v___x_2003_ = l_Lean_LocalDecl_userName(v_val_2002_);
v___x_2004_ = l_Lean_Name_hasMacroScopes(v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Core_mkFreshUserName(v___x_2003_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v___x_2007_ = l_Lean_LocalDecl_fvarId(v_val_2002_);
lean_dec(v_val_2002_);
v___x_2008_ = l_Lean_LocalContext_setUserName(v_b_1989_, v___x_2007_, v_a_2006_);
v_a_1997_ = v___x_2008_;
goto v___jp_1996_;
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_val_2002_);
lean_dec(v_i_1990_);
lean_dec_ref(v_b_1989_);
v_a_2009_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2005_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2005_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
else
{
lean_dec(v___x_2003_);
lean_dec(v_val_2002_);
v_a_1997_ = v_b_1989_;
goto v___jp_1996_;
}
}
else
{
lean_dec(v___y_2001_);
v_a_1997_ = v_b_1989_;
goto v___jp_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_range_2025_, lean_object* v_b_2026_, lean_object* v_i_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_2025_, v_b_2026_, v_i_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v_range_2025_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(lean_object* v_lctx_2032_, lean_object* v_idx_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_inc_ref(v_lctx_2032_);
v___x_2041_ = lean_local_ctx_num_indices(v_lctx_2032_);
v___x_2042_ = lean_unsigned_to_nat(1u);
lean_inc(v_idx_2033_);
v___x_2043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2043_, 0, v_idx_2033_);
lean_ctor_set(v___x_2043_, 1, v___x_2041_);
lean_ctor_set(v___x_2043_, 2, v___x_2042_);
v___x_2044_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v___x_2043_, v_lctx_2032_, v_idx_2033_, v___y_2038_, v___y_2039_);
lean_dec_ref_known(v___x_2043_, 3);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0___boxed(lean_object* v_lctx_2045_, lean_object* v_idx_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_2045_, v_idx_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
return v_res_2054_;
}
}
static lean_object* _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__0));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(lean_object* v_mvarId_2058_, lean_object* v_idx_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v_mctx_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_st_ref_get(v___y_2063_);
v_mctx_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_mctx_2068_);
lean_dec(v___x_2067_);
v___x_2069_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2068_, v_mvarId_2058_);
lean_dec_ref(v_mctx_2068_);
if (lean_obj_tag(v___x_2069_) == 1)
{
lean_object* v_val_2070_; lean_object* v_userName_2071_; lean_object* v_lctx_2072_; lean_object* v_type_2073_; lean_object* v_depth_2074_; lean_object* v_localInstances_2075_; uint8_t v_kind_2076_; lean_object* v_numScopeArgs_2077_; lean_object* v_index_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2136_; 
v_val_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v_userName_2071_ = lean_ctor_get(v_val_2070_, 0);
v_lctx_2072_ = lean_ctor_get(v_val_2070_, 1);
v_type_2073_ = lean_ctor_get(v_val_2070_, 2);
v_depth_2074_ = lean_ctor_get(v_val_2070_, 3);
v_localInstances_2075_ = lean_ctor_get(v_val_2070_, 4);
v_kind_2076_ = lean_ctor_get_uint8(v_val_2070_, sizeof(void*)*7);
v_numScopeArgs_2077_ = lean_ctor_get(v_val_2070_, 5);
v_index_2078_ = lean_ctor_get(v_val_2070_, 6);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_val_2070_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2080_ = v_val_2070_;
v_isShared_2081_ = v_isSharedCheck_2136_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_index_2078_);
lean_inc(v_numScopeArgs_2077_);
lean_inc(v_localInstances_2075_);
lean_inc(v_depth_2074_);
lean_inc(v_type_2073_);
lean_inc(v_lctx_2072_);
lean_inc(v_userName_2071_);
lean_dec(v_val_2070_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2136_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0(v_lctx_2072_, v_idx_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2127_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2127_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2127_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v_mctx_2088_; lean_object* v_cache_2089_; lean_object* v_zetaDeltaFVarIds_2090_; lean_object* v_postponed_2091_; lean_object* v_diag_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2126_; 
v___x_2087_ = lean_st_ref_take(v___y_2063_);
v_mctx_2088_ = lean_ctor_get(v___x_2087_, 0);
v_cache_2089_ = lean_ctor_get(v___x_2087_, 1);
v_zetaDeltaFVarIds_2090_ = lean_ctor_get(v___x_2087_, 2);
v_postponed_2091_ = lean_ctor_get(v___x_2087_, 3);
v_diag_2092_ = lean_ctor_get(v___x_2087_, 4);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2094_ = v___x_2087_;
v_isShared_2095_ = v_isSharedCheck_2126_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_diag_2092_);
lean_inc(v_postponed_2091_);
lean_inc(v_zetaDeltaFVarIds_2090_);
lean_inc(v_cache_2089_);
lean_inc(v_mctx_2088_);
lean_dec(v___x_2087_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2126_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_depth_2096_; lean_object* v_levelAssignDepth_2097_; lean_object* v_lmvarCounter_2098_; lean_object* v_mvarCounter_2099_; lean_object* v_lDecls_2100_; lean_object* v_decls_2101_; lean_object* v_userNames_2102_; lean_object* v_lAssignment_2103_; lean_object* v_eAssignment_2104_; lean_object* v_dAssignment_2105_; lean_object* v_instanceTypedMVars_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2125_; 
v_depth_2096_ = lean_ctor_get(v_mctx_2088_, 0);
v_levelAssignDepth_2097_ = lean_ctor_get(v_mctx_2088_, 1);
v_lmvarCounter_2098_ = lean_ctor_get(v_mctx_2088_, 2);
v_mvarCounter_2099_ = lean_ctor_get(v_mctx_2088_, 3);
v_lDecls_2100_ = lean_ctor_get(v_mctx_2088_, 4);
v_decls_2101_ = lean_ctor_get(v_mctx_2088_, 5);
v_userNames_2102_ = lean_ctor_get(v_mctx_2088_, 6);
v_lAssignment_2103_ = lean_ctor_get(v_mctx_2088_, 7);
v_eAssignment_2104_ = lean_ctor_get(v_mctx_2088_, 8);
v_dAssignment_2105_ = lean_ctor_get(v_mctx_2088_, 9);
v_instanceTypedMVars_2106_ = lean_ctor_get(v_mctx_2088_, 10);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_mctx_2088_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2108_ = v_mctx_2088_;
v_isShared_2109_ = v_isSharedCheck_2125_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_instanceTypedMVars_2106_);
lean_inc(v_dAssignment_2105_);
lean_inc(v_eAssignment_2104_);
lean_inc(v_lAssignment_2103_);
lean_inc(v_userNames_2102_);
lean_inc(v_decls_2101_);
lean_inc(v_lDecls_2100_);
lean_inc(v_mvarCounter_2099_);
lean_inc(v_lmvarCounter_2098_);
lean_inc(v_levelAssignDepth_2097_);
lean_inc(v_depth_2096_);
lean_dec(v_mctx_2088_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2125_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 1, v_a_2083_);
v___x_2111_ = v___x_2080_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_userName_2071_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_a_2083_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_type_2073_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_depth_2074_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_localInstances_2075_);
lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_numScopeArgs_2077_);
lean_ctor_set(v_reuseFailAlloc_2124_, 6, v_index_2078_);
lean_ctor_set_uint8(v_reuseFailAlloc_2124_, sizeof(void*)*7, v_kind_2076_);
v___x_2111_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_decls_2101_, v_mvarId_2058_, v___x_2111_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 5, v___x_2112_);
v___x_2114_ = v___x_2108_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_depth_2096_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_levelAssignDepth_2097_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_lmvarCounter_2098_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_mvarCounter_2099_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v_lDecls_2100_);
lean_ctor_set(v_reuseFailAlloc_2123_, 5, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2123_, 6, v_userNames_2102_);
lean_ctor_set(v_reuseFailAlloc_2123_, 7, v_lAssignment_2103_);
lean_ctor_set(v_reuseFailAlloc_2123_, 8, v_eAssignment_2104_);
lean_ctor_set(v_reuseFailAlloc_2123_, 9, v_dAssignment_2105_);
lean_ctor_set(v_reuseFailAlloc_2123_, 10, v_instanceTypedMVars_2106_);
v___x_2114_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2114_);
v___x_2116_ = v___x_2094_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_cache_2089_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_zetaDeltaFVarIds_2090_);
lean_ctor_set(v_reuseFailAlloc_2122_, 3, v_postponed_2091_);
lean_ctor_set(v_reuseFailAlloc_2122_, 4, v_diag_2092_);
v___x_2116_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2117_ = lean_st_ref_put(v___y_2063_, v___x_2116_);
v___x_2118_ = lean_box(0);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2118_);
v___x_2120_ = v___x_2085_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
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
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_del_object(v___x_2080_);
lean_dec(v_index_2078_);
lean_dec(v_numScopeArgs_2077_);
lean_dec_ref(v_localInstances_2075_);
lean_dec(v_depth_2074_);
lean_dec_ref(v_type_2073_);
lean_dec(v_userName_2071_);
lean_dec(v_mvarId_2058_);
v_a_2128_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2082_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2082_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec(v___x_2069_);
lean_dec(v_idx_2059_);
v___x_2137_ = lean_obj_once(&l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1, &l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1_once, _init_l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___closed__1);
v___x_2138_ = l_Lean_MessageData_ofName(v_mvarId_2058_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2139_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
return v___x_2140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0___boxed(lean_object* v_mvarId_2141_, lean_object* v_idx_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_mvarId_2141_, v_idx_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC(lean_object* v_goal_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v_initialCtxSize_2159_; lean_object* v___x_2160_; 
v_initialCtxSize_2159_ = lean_ctor_get(v_a_2152_, 5);
lean_inc(v_initialCtxSize_2159_);
lean_inc(v_goal_2151_);
v___x_2160_ = l_Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0(v_goal_2151_, v_initialCtxSize_2159_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v___x_2161_; 
lean_dec_ref_known(v___x_2160_, 1);
lean_inc(v_goal_2151_);
v___x_2161_ = l_Lean_MVarId_getType(v_goal_2151_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = 2;
lean_inc(v_goal_2151_);
v___x_2164_ = l_Lean_MVarId_setKind___redArg(v_goal_2151_, v___x_2163_, v_a_2155_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2207_; 
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; 
v_unused_2208_ = lean_ctor_get(v___x_2164_, 0);
lean_dec(v_unused_2208_);
v___x_2166_ = v___x_2164_;
v_isShared_2167_ = v_isSharedCheck_2207_;
goto v_resetjp_2165_;
}
else
{
lean_dec(v___x_2164_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2207_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v_env_2169_; uint8_t v___x_2170_; 
v___x_2168_ = lean_st_ref_get(v_a_2157_);
v_env_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_ref(v_env_2169_);
lean_dec(v___x_2168_);
v___x_2170_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v_env_2169_, v_a_2162_);
lean_dec(v_a_2162_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v_fuel_2172_; lean_object* v_simpState_2173_; lean_object* v_invariants_2174_; lean_object* v_vcs_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2188_; 
v___x_2171_ = lean_st_ref_take(v_a_2153_);
v_fuel_2172_ = lean_ctor_get(v___x_2171_, 0);
v_simpState_2173_ = lean_ctor_get(v___x_2171_, 1);
v_invariants_2174_ = lean_ctor_get(v___x_2171_, 2);
v_vcs_2175_ = lean_ctor_get(v___x_2171_, 3);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2177_ = v___x_2171_;
v_isShared_2178_ = v_isSharedCheck_2188_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_vcs_2175_);
lean_inc(v_invariants_2174_);
lean_inc(v_simpState_2173_);
lean_inc(v_fuel_2172_);
lean_dec(v___x_2171_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2188_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2179_ = lean_array_push(v_vcs_2175_, v_goal_2151_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 3, v___x_2179_);
v___x_2181_ = v___x_2177_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_fuel_2172_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_simpState_2173_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_invariants_2174_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2182_ = lean_st_ref_put(v_a_2153_, v___x_2181_);
v___x_2183_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2183_);
v___x_2185_ = v___x_2166_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v___x_2189_; lean_object* v_fuel_2190_; lean_object* v_simpState_2191_; lean_object* v_invariants_2192_; lean_object* v_vcs_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2206_; 
v___x_2189_ = lean_st_ref_take(v_a_2153_);
v_fuel_2190_ = lean_ctor_get(v___x_2189_, 0);
v_simpState_2191_ = lean_ctor_get(v___x_2189_, 1);
v_invariants_2192_ = lean_ctor_get(v___x_2189_, 2);
v_vcs_2193_ = lean_ctor_get(v___x_2189_, 3);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2195_ = v___x_2189_;
v_isShared_2196_ = v_isSharedCheck_2206_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_vcs_2193_);
lean_inc(v_invariants_2192_);
lean_inc(v_simpState_2191_);
lean_inc(v_fuel_2190_);
lean_dec(v___x_2189_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2206_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_array_push(v_invariants_2192_, v_goal_2151_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 2, v___x_2197_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_fuel_2190_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_simpState_2191_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_vcs_2193_);
v___x_2199_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2200_ = lean_st_ref_put(v_a_2153_, v___x_2199_);
v___x_2201_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2201_);
v___x_2203_ = v___x_2166_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2162_);
lean_dec(v_goal_2151_);
return v___x_2164_;
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec(v_goal_2151_);
v_a_2209_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2161_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2161_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_dec(v_goal_2151_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addSubGoalAsVC___boxed(lean_object* v_goal_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v_goal_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1(lean_object* v_00_u03b2_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1___redArg(v_x_2227_, v_x_2228_, v_x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(lean_object* v_range_2231_, lean_object* v_b_2232_, lean_object* v_i_2233_, lean_object* v_hs_2234_, lean_object* v_hl_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___redArg(v_range_2231_, v_b_2232_, v_i_2233_, v___y_2240_, v___y_2241_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1___boxed(lean_object* v_range_2244_, lean_object* v_b_2245_, lean_object* v_i_2246_, lean_object* v_hs_2247_, lean_object* v_hl_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Basic_0__Lean_Meta_freshenUserNamesSinceIdx___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__0_spec__1(v_range_2244_, v_b_2245_, v_i_2246_, v_hs_2247_, v_hl_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_range_2244_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2257_, lean_object* v_x_2258_, size_t v_x_2259_, size_t v_x_2260_, lean_object* v_x_2261_, lean_object* v_x_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___redArg(v_x_2258_, v_x_2259_, v_x_2260_, v_x_2261_, v_x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
size_t v_x_7678__boxed_2270_; size_t v_x_7679__boxed_2271_; lean_object* v_res_2272_; 
v_x_7678__boxed_2270_ = lean_unbox_usize(v_x_2266_);
lean_dec(v_x_2266_);
v_x_7679__boxed_2271_ = lean_unbox_usize(v_x_2267_);
lean_dec(v_x_2267_);
v_res_2272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3(v_00_u03b2_2264_, v_x_2265_, v_x_7678__boxed_2270_, v_x_7679__boxed_2271_, v_x_2268_, v_x_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2273_, lean_object* v_n_2274_, lean_object* v_k_2275_, lean_object* v_v_2276_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4___redArg(v_n_2274_, v_k_2275_, v_v_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2278_, size_t v_depth_2279_, lean_object* v_keys_2280_, lean_object* v_vals_2281_, lean_object* v_heq_2282_, lean_object* v_i_2283_, lean_object* v_entries_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___redArg(v_depth_2279_, v_keys_2280_, v_vals_2281_, v_i_2283_, v_entries_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2286_, lean_object* v_depth_2287_, lean_object* v_keys_2288_, lean_object* v_vals_2289_, lean_object* v_heq_2290_, lean_object* v_i_2291_, lean_object* v_entries_2292_){
_start:
{
size_t v_depth_boxed_2293_; lean_object* v_res_2294_; 
v_depth_boxed_2293_ = lean_unbox_usize(v_depth_2287_);
lean_dec(v_depth_2287_);
v_res_2294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__5(v_00_u03b2_2286_, v_depth_boxed_2293_, v_keys_2288_, v_vals_2289_, v_heq_2290_, v_i_2291_, v_entries_2292_);
lean_dec_ref(v_vals_2289_);
lean_dec_ref(v_keys_2288_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_freshenLCtxUserNamesSinceIdx___at___00Lean_Elab_Tactic_Do_addSubGoalAsVC_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2296_, v_x_2297_, v_x_2298_, v_x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC(lean_object* v_subGoal_2301_, lean_object* v_name_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_subGoal_2301_, v_name_2302_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = l_Lean_Expr_mvarId_x21(v_a_2311_);
v___x_2313_ = l_Lean_Elab_Tactic_Do_addSubGoalAsVC(v___x_2312_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v___x_2313_, 0);
lean_dec(v_unused_2321_);
v___x_2315_ = v___x_2313_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v___x_2313_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v_a_2311_);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2311_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_2311_);
v_a_2322_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2313_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2313_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
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
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_emitVC___boxed(lean_object* v_subGoal_2330_, lean_object* v_name_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Elab_Tactic_Do_emitVC(v_subGoal_2330_, v_name_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg(lean_object* v_x_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; lean_object* v_fuel_2349_; lean_object* v_simpState_2350_; lean_object* v_invariants_2351_; lean_object* v_vcs_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2375_; 
v___x_2348_ = lean_st_ref_get(v_a_2342_);
v_fuel_2349_ = lean_ctor_get(v___x_2348_, 0);
v_simpState_2350_ = lean_ctor_get(v___x_2348_, 1);
v_invariants_2351_ = lean_ctor_get(v___x_2348_, 2);
v_vcs_2352_ = lean_ctor_get(v___x_2348_, 3);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2354_ = v___x_2348_;
v_isShared_2355_ = v_isSharedCheck_2375_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_vcs_2352_);
lean_inc(v_invariants_2351_);
lean_inc(v_simpState_2350_);
lean_inc(v_fuel_2349_);
lean_dec(v___x_2348_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2375_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v_simpCtx_2357_; lean_object* v_simprocs_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2356_ = lean_st_mk_ref(v_simpState_2350_);
v_simpCtx_2357_ = lean_ctor_get(v_a_2341_, 2);
v_simprocs_2358_ = lean_ctor_get(v_a_2341_, 3);
lean_inc_ref(v_simprocs_2358_);
v___x_2359_ = l_Lean_Meta_Simp_mkDefaultMethodsCore(v_simprocs_2358_);
v___x_2360_ = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(v___x_2359_);
lean_dec_ref(v___x_2359_);
lean_inc(v_a_2346_);
lean_inc_ref(v_a_2345_);
lean_inc(v_a_2344_);
lean_inc_ref(v_a_2343_);
lean_inc(v___x_2356_);
lean_inc_ref(v_simpCtx_2357_);
v___x_2361_ = lean_apply_8(v_x_2340_, v___x_2360_, v_simpCtx_2357_, v___x_2356_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, lean_box(0));
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2374_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2374_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2374_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_st_ref_get(v___x_2356_);
lean_dec(v___x_2356_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v___x_2366_);
v___x_2368_ = v___x_2354_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_fuel_2349_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_invariants_2351_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_vcs_2352_);
v___x_2368_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_st_ref_swap(v_a_2342_, v___x_2368_);
lean_dec(v___x_2369_);
if (v_isShared_2365_ == 0)
{
v___x_2371_ = v___x_2364_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2362_);
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
else
{
lean_dec(v___x_2356_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_vcs_2352_);
lean_dec_ref(v_invariants_2351_);
lean_dec(v_fuel_2349_);
return v___x_2361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___redArg___boxed(lean_object* v_x_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM(lean_object* v_00_u03b1_2385_, lean_object* v_x_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_liftSimpM___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_x_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Elab_Tactic_Do_liftSimpM(v_00_u03b1_2395_, v_x_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(lean_object* v_00_u03b1_2405_, lean_object* v_x_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v_x_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0___boxed(lean_object* v_00_u03b1_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___lam__0(v_00_u03b1_2415_, v_x_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg(lean_object* v_jp_2427_, lean_object* v_info_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_config_2437_; lean_object* v_specThms_2438_; lean_object* v_simpCtx_2439_; lean_object* v_simprocs_2440_; lean_object* v_jps_2441_; lean_object* v_initialCtxSize_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_config_2437_ = lean_ctor_get(v_a_2430_, 0);
v_specThms_2438_ = lean_ctor_get(v_a_2430_, 1);
v_simpCtx_2439_ = lean_ctor_get(v_a_2430_, 2);
v_simprocs_2440_ = lean_ctor_get(v_a_2430_, 3);
v_jps_2441_ = lean_ctor_get(v_a_2430_, 4);
v_initialCtxSize_2442_ = lean_ctor_get(v_a_2430_, 5);
lean_inc(v_jps_2441_);
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_jp_2427_, v_info_2428_, v_jps_2441_);
lean_inc(v_initialCtxSize_2442_);
lean_inc_ref(v_simprocs_2440_);
lean_inc_ref(v_simpCtx_2439_);
lean_inc_ref(v_specThms_2438_);
lean_inc_ref(v_config_2437_);
v___x_2444_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2444_, 0, v_config_2437_);
lean_ctor_set(v___x_2444_, 1, v_specThms_2438_);
lean_ctor_set(v___x_2444_, 2, v_simpCtx_2439_);
lean_ctor_set(v___x_2444_, 3, v_simprocs_2440_);
lean_ctor_set(v___x_2444_, 4, v___x_2443_);
lean_ctor_set(v___x_2444_, 5, v_initialCtxSize_2442_);
lean_inc(v_a_2435_);
lean_inc_ref(v_a_2434_);
lean_inc(v_a_2433_);
lean_inc_ref(v_a_2432_);
lean_inc(v_a_2431_);
v___x_2445_ = lean_apply_7(v_a_2429_, v___x_2444_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, lean_box(0));
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___redArg___boxed(lean_object* v_jp_2446_, lean_object* v_info_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_2446_, v_info_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP(lean_object* v_00_u03b1_2457_, lean_object* v_jp_2458_, lean_object* v_info_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Elab_Tactic_Do_withJP___redArg(v_jp_2458_, v_info_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withJP___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_jp_2470_, lean_object* v_info_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Elab_Tactic_Do_withJP(v_00_u03b1_2469_, v_jp_2470_, v_info_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(lean_object* v_t_2481_, lean_object* v_k_2482_){
_start:
{
if (lean_obj_tag(v_t_2481_) == 0)
{
lean_object* v_k_2483_; lean_object* v_v_2484_; lean_object* v_l_2485_; lean_object* v_r_2486_; uint8_t v___x_2487_; 
v_k_2483_ = lean_ctor_get(v_t_2481_, 1);
v_v_2484_ = lean_ctor_get(v_t_2481_, 2);
v_l_2485_ = lean_ctor_get(v_t_2481_, 3);
v_r_2486_ = lean_ctor_get(v_t_2481_, 4);
v___x_2487_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2482_, v_k_2483_);
switch(v___x_2487_)
{
case 0:
{
v_t_2481_ = v_l_2485_;
goto _start;
}
case 1:
{
lean_object* v___x_2489_; 
lean_inc(v_v_2484_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_v_2484_);
return v___x_2489_;
}
default: 
{
v_t_2481_ = v_r_2486_;
goto _start;
}
}
}
else
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_2492_, lean_object* v_k_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_2492_, v_k_2493_);
lean_dec(v_k_2493_);
lean_dec(v_t_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(lean_object* v_jp_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_jps_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_jps_2498_ = lean_ctor_get(v_a_2496_, 4);
v___x_2499_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_jps_2498_, v_jp_2495_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg___boxed(lean_object* v_jp_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_2501_, v_a_2502_);
lean_dec_ref(v_a_2502_);
lean_dec(v_jp_2501_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f(lean_object* v_jp_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Elab_Tactic_Do_knownJP_x3f___redArg(v_jp_2505_, v_a_2506_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_knownJP_x3f___boxed(lean_object* v_jp_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Elab_Tactic_Do_knownJP_x3f(v_jp_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_jp_2514_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(lean_object* v_00_u03b4_2523_, lean_object* v_t_2524_, lean_object* v_k_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___redArg(v_t_2524_, v_k_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_2527_, lean_object* v_t_2528_, lean_object* v_k_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_knownJP_x3f_spec__0(v_00_u03b4_2527_, v_t_2528_, v_k_2529_);
lean_dec(v_k_2529_);
lean_dec(v_t_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isDuplicable(lean_object* v_e_2536_){
_start:
{
switch(lean_obj_tag(v_e_2536_))
{
case 5:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isDuplicable___closed__2));
v___x_2538_ = l_Lean_Expr_isAppOf(v_e_2536_, v___x_2537_);
return v___x_2538_;
}
case 6:
{
uint8_t v___x_2539_; 
v___x_2539_ = 0;
return v___x_2539_;
}
case 7:
{
uint8_t v___x_2540_; 
v___x_2540_ = 0;
return v___x_2540_;
}
case 8:
{
uint8_t v___x_2541_; 
v___x_2541_ = 0;
return v___x_2541_;
}
case 10:
{
lean_object* v_expr_2542_; 
v_expr_2542_ = lean_ctor_get(v_e_2536_, 1);
v_e_2536_ = v_expr_2542_;
goto _start;
}
case 11:
{
lean_object* v_struct_2544_; 
v_struct_2544_ = lean_ctor_get(v_e_2536_, 2);
v_e_2536_ = v_struct_2544_;
goto _start;
}
default: 
{
uint8_t v___x_2546_; 
v___x_2546_ = 1;
return v___x_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isDuplicable___boxed(lean_object* v_e_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_e_2547_);
lean_dec_ref(v_e_2547_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(lean_object* v_k_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v_b_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2552_);
lean_inc_ref(v___y_2551_);
v___x_2559_ = lean_apply_8(v_k_2550_, v_b_2553_, v___y_2551_, v___y_2552_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, lean_box(0));
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed(lean_object* v_k_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v_b_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0(v_k_2560_, v___y_2561_, v___y_2562_, v_b_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(lean_object* v_name_2570_, lean_object* v_type_2571_, lean_object* v_val_2572_, lean_object* v_k_2573_, uint8_t v_nondep_2574_, uint8_t v_kind_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___f_2583_; lean_object* v___x_2584_; 
lean_inc(v___y_2577_);
lean_inc_ref(v___y_2576_);
v___f_2583_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2583_, 0, v_k_2573_);
lean_closure_set(v___f_2583_, 1, v___y_2576_);
lean_closure_set(v___f_2583_, 2, v___y_2577_);
v___x_2584_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2570_, v_type_2571_, v_val_2572_, v___f_2583_, v_nondep_2574_, v_kind_2575_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2584_) == 0)
{
return v___x_2584_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg___boxed(lean_object* v_name_2593_, lean_object* v_type_2594_, lean_object* v_val_2595_, lean_object* v_k_2596_, lean_object* v_nondep_2597_, lean_object* v_kind_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
uint8_t v_nondep_boxed_2606_; uint8_t v_kind_boxed_2607_; lean_object* v_res_2608_; 
v_nondep_boxed_2606_ = lean_unbox(v_nondep_2597_);
v_kind_boxed_2607_ = lean_unbox(v_kind_2598_);
v_res_2608_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2593_, v_type_2594_, v_val_2595_, v_k_2596_, v_nondep_boxed_2606_, v_kind_boxed_2607_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(lean_object* v_00_u03b1_2609_, lean_object* v_name_2610_, lean_object* v_type_2611_, lean_object* v_val_2612_, lean_object* v_k_2613_, uint8_t v_nondep_2614_, uint8_t v_kind_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2610_, v_type_2611_, v_val_2612_, v_k_2613_, v_nondep_2614_, v_kind_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___boxed(lean_object* v_00_u03b1_2624_, lean_object* v_name_2625_, lean_object* v_type_2626_, lean_object* v_val_2627_, lean_object* v_k_2628_, lean_object* v_nondep_2629_, lean_object* v_kind_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v_nondep_boxed_2638_; uint8_t v_kind_boxed_2639_; lean_object* v_res_2640_; 
v_nondep_boxed_2638_ = lean_unbox(v_nondep_2629_);
v_kind_boxed_2639_ = lean_unbox(v_kind_2630_);
v_res_2640_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0(v_00_u03b1_2624_, v_name_2625_, v_type_2626_, v_val_2627_, v_k_2628_, v_nondep_boxed_2638_, v_kind_boxed_2639_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(lean_object* v___x_2641_, lean_object* v_x_2642_, uint8_t v___x_2643_, uint8_t v___x_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Meta_mkLetFVars(v___x_2641_, v_x_2642_, v___x_2643_, v___x_2643_, v___x_2644_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed(lean_object* v___x_2654_, lean_object* v_x_2655_, lean_object* v___x_2656_, lean_object* v___x_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v___x_1434__boxed_2666_; uint8_t v___x_1435__boxed_2667_; lean_object* v_res_2668_; 
v___x_1434__boxed_2666_ = lean_unbox(v___x_2656_);
v___x_1435__boxed_2667_ = lean_unbox(v___x_2657_);
v_res_2668_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0(v___x_2654_, v_x_2655_, v___x_1434__boxed_2666_, v___x_1435__boxed_2667_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___x_2654_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(lean_object* v_fv_2669_, uint8_t v___x_2670_, lean_object* v_x_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___f_2685_; lean_object* v___x_2686_; 
v___x_2679_ = lean_unsigned_to_nat(1u);
v___x_2680_ = lean_mk_empty_array_with_capacity(v___x_2679_);
v___x_2681_ = lean_array_push(v___x_2680_, v_fv_2669_);
v___x_2682_ = 1;
v___x_2683_ = lean_box(v___x_2670_);
v___x_2684_ = lean_box(v___x_2682_);
v___f_2685_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_2685_, 0, v___x_2681_);
lean_closure_set(v___f_2685_, 1, v_x_2671_);
lean_closure_set(v___f_2685_, 2, v___x_2683_);
lean_closure_set(v___f_2685_, 3, v___x_2684_);
v___x_2686_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_2685_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed(lean_object* v_fv_2687_, lean_object* v___x_2688_, lean_object* v_x_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v___x_1470__boxed_2697_; lean_object* v_res_2698_; 
v___x_1470__boxed_2697_ = lean_unbox(v___x_2688_);
v_res_2698_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1(v_fv_2687_, v___x_1470__boxed_2697_, v_x_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(uint8_t v___x_2699_, lean_object* v_k_2700_, lean_object* v_fv_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2709_ = lean_box(v___x_2699_);
lean_inc_ref(v_fv_2701_);
v___f_2710_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2710_, 0, v_fv_2701_);
lean_closure_set(v___f_2710_, 1, v___x_2709_);
v___x_2711_ = lean_box(v___x_2699_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
v___x_2712_ = lean_apply_10(v_k_2700_, v___x_2711_, v_fv_2701_, v___f_2710_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, lean_box(0));
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed(lean_object* v___x_2713_, lean_object* v_k_2714_, lean_object* v_fv_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v___x_1513__boxed_2723_; lean_object* v_res_2724_; 
v___x_1513__boxed_2723_ = lean_unbox(v___x_2713_);
v_res_2724_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2(v___x_1513__boxed_2723_, v_k_2714_, v_fv_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___y_2725_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3___boxed(lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__3(v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(lean_object* v_name_2744_, lean_object* v_type_2745_, lean_object* v_val_2746_, lean_object* v_k_2747_, uint8_t v_kind_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
uint8_t v___x_2756_; 
v___x_2756_ = l_Lean_Elab_Tactic_Do_isDuplicable(v_val_2746_);
if (v___x_2756_ == 0)
{
uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___f_2759_; lean_object* v___x_2760_; 
v___x_2757_ = 1;
v___x_2758_ = lean_box(v___x_2757_);
v___f_2759_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___lam__2___boxed), 10, 2);
lean_closure_set(v___f_2759_, 0, v___x_2758_);
lean_closure_set(v___f_2759_, 1, v_k_2747_);
v___x_2760_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_withLetDeclShared_spec__0___redArg(v_name_2744_, v_type_2745_, v_val_2746_, v___f_2759_, v___x_2756_, v_kind_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
return v___x_2760_;
}
else
{
lean_object* v___f_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec_ref(v_type_2745_);
lean_dec(v_name_2744_);
v___f_2761_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___closed__0));
v___x_2762_ = 0;
v___x_2763_ = lean_box(v___x_2762_);
lean_inc(v_a_2754_);
lean_inc_ref(v_a_2753_);
lean_inc(v_a_2752_);
lean_inc_ref(v_a_2751_);
lean_inc(v_a_2750_);
lean_inc_ref(v_a_2749_);
v___x_2764_ = lean_apply_10(v_k_2747_, v___x_2763_, v_val_2746_, v___f_2761_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, lean_box(0));
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg___boxed(lean_object* v_name_2765_, lean_object* v_type_2766_, lean_object* v_val_2767_, lean_object* v_k_2768_, lean_object* v_kind_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
uint8_t v_kind_boxed_2777_; lean_object* v_res_2778_; 
v_kind_boxed_2777_ = lean_unbox(v_kind_2769_);
v_res_2778_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2765_, v_type_2766_, v_val_2767_, v_k_2768_, v_kind_boxed_2777_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared(lean_object* v_00_u03b1_2779_, lean_object* v_name_2780_, lean_object* v_type_2781_, lean_object* v_val_2782_, lean_object* v_k_2783_, uint8_t v_kind_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Elab_Tactic_Do_withLetDeclShared___redArg(v_name_2780_, v_type_2781_, v_val_2782_, v_k_2783_, v_kind_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLetDeclShared___boxed(lean_object* v_00_u03b1_2793_, lean_object* v_name_2794_, lean_object* v_type_2795_, lean_object* v_val_2796_, lean_object* v_k_2797_, lean_object* v_kind_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
uint8_t v_kind_boxed_2806_; lean_object* v_res_2807_; 
v_kind_boxed_2806_ = lean_unbox(v_kind_2798_);
v_res_2807_ = l_Lean_Elab_Tactic_Do_withLetDeclShared(v_00_u03b1_2793_, v_name_2794_, v_type_2795_, v_val_2796_, v_k_2797_, v_kind_boxed_2806_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
return v_res_2807_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object* v_n_2811_){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2812_ = l_Lean_Name_eraseMacroScopes(v_n_2811_);
v___x_2813_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_isJP___closed__1));
v___x_2814_ = lean_name_eq(v___x_2812_, v___x_2813_);
lean_dec(v___x_2812_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_isJP___boxed(lean_object* v_n_2815_){
_start:
{
uint8_t v_res_2816_; lean_object* v_r_2817_; 
v_res_2816_ = l_Lean_Elab_Tactic_Do_isJP(v_n_2815_);
lean_dec(v_n_2815_);
v_r_2817_ = lean_box(v_res_2816_);
return v_r_2817_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__0));
v___x_2820_ = l_Lean_stringToMessageData(v___x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams(lean_object* v_joinTy_2821_, lean_object* v_resTy_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = l_Lean_Expr_isMData(v_joinTy_2821_);
if (v___x_2828_ == 0)
{
uint8_t v___x_2829_; 
v___x_2829_ = lean_expr_eqv(v_joinTy_2821_, v_resTy_2822_);
if (v___x_2829_ == 0)
{
uint8_t v___x_2830_; 
v___x_2830_ = l_Lean_Expr_isForall(v_joinTy_2821_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2831_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1, &l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1_once, _init_l_Lean_Elab_Tactic_Do_getNumJoinParams___closed__1);
v___x_2832_ = l_Lean_MessageData_ofExpr(v_joinTy_2821_);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_2833_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = l_Lean_Expr_consumeMData(v_joinTy_2821_);
lean_dec_ref(v_joinTy_2821_);
v___x_2836_ = l_Lean_Expr_bindingBody_x21(v___x_2835_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v___x_2836_, v_resTy_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2847_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2842_ = lean_unsigned_to_nat(1u);
v___x_2843_ = lean_nat_add(v___x_2842_, v_a_2838_);
lean_dec(v_a_2838_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
return v___x_2837_;
}
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v_joinTy_2821_);
v___x_2848_ = lean_unsigned_to_nat(0u);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
else
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Expr_consumeMData(v_joinTy_2821_);
lean_dec_ref(v_joinTy_2821_);
v_joinTy_2821_ = v___x_2850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getNumJoinParams___boxed(lean_object* v_joinTy_2852_, lean_object* v_resTy_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_Elab_Tactic_Do_getNumJoinParams(v_joinTy_2852_, v_resTy_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec_ref(v_resTy_2853_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(lean_object* v_lastReduction_2861_, lean_object* v_f_2862_, lean_object* v_rargs_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
switch(lean_obj_tag(v_f_2862_))
{
case 10:
{
lean_object* v_expr_2869_; 
v_expr_2869_ = lean_ctor_get(v_f_2862_, 1);
lean_inc_ref(v_expr_2869_);
lean_dec_ref_known(v_f_2862_, 2);
v_f_2862_ = v_expr_2869_;
goto _start;
}
case 5:
{
lean_object* v_fn_2871_; lean_object* v_arg_2872_; lean_object* v___x_2873_; 
v_fn_2871_ = lean_ctor_get(v_f_2862_, 0);
lean_inc_ref(v_fn_2871_);
v_arg_2872_ = lean_ctor_get(v_f_2862_, 1);
lean_inc_ref(v_arg_2872_);
lean_dec_ref_known(v_f_2862_, 2);
v___x_2873_ = lean_array_push(v_rargs_2863_, v_arg_2872_);
v_f_2862_ = v_fn_2871_;
v_rargs_2863_ = v___x_2873_;
goto _start;
}
case 6:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2875_ = lean_array_get_size(v_rargs_2863_);
v___x_2876_ = lean_unsigned_to_nat(0u);
v___x_2877_ = lean_nat_dec_eq(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v_e_x27_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec(v_lastReduction_2861_);
v_e_x27_2878_ = l_Lean_Expr_betaRev(v_f_2862_, v_rargs_2863_, v___x_2877_, v___x_2877_);
lean_dec_ref(v_rargs_2863_);
lean_inc_ref(v_e_x27_2878_);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v_e_x27_2878_);
v___x_2880_ = l_Lean_Expr_getAppFn(v_e_x27_2878_);
v___x_2881_ = l_Lean_Expr_getAppNumArgs(v_e_x27_2878_);
v___x_2882_ = lean_mk_empty_array_with_capacity(v___x_2881_);
lean_dec(v___x_2881_);
v___x_2883_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_x27_2878_, v___x_2882_);
v_lastReduction_2861_ = v___x_2879_;
v_f_2862_ = v___x_2880_;
v_rargs_2863_ = v___x_2883_;
goto _start;
}
else
{
lean_object* v___x_2885_; 
lean_dec_ref_known(v_f_2862_, 3);
lean_dec_ref(v_rargs_2863_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_lastReduction_2861_);
return v___x_2885_;
}
}
case 4:
{
lean_object* v_declName_2886_; lean_object* v___x_2887_; lean_object* v_env_2888_; lean_object* v___x_2889_; 
v_declName_2886_ = lean_ctor_get(v_f_2862_, 0);
v___x_2887_ = lean_st_ref_get(v_a_2867_);
v_env_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc_ref(v_env_2888_);
lean_dec(v___x_2887_);
lean_inc(v_declName_2886_);
v___x_2889_ = l_Lean_Environment_getProjectionStructureName_x3f(v_env_2888_, v_declName_2886_);
if (lean_obj_tag(v___x_2889_) == 1)
{
lean_object* v_val_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2924_; 
v_val_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2924_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_val_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2924_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
if (lean_obj_tag(v_val_2890_) == 1)
{
lean_object* v_pre_2894_; 
v_pre_2894_ = lean_ctor_get(v_val_2890_, 0);
if (lean_obj_tag(v_pre_2894_) == 0)
{
lean_object* v_str_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_str_2895_ = lean_ctor_get(v_val_2890_, 1);
lean_inc_ref(v_str_2895_);
lean_dec_ref_known(v_val_2890_, 2);
v___x_2896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___closed__0));
v___x_2897_ = lean_string_dec_eq(v_str_2895_, v___x_2896_);
lean_dec_ref(v_str_2895_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref_known(v_f_2862_, 2);
lean_dec_ref(v_rargs_2863_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 0);
lean_ctor_set(v___x_2892_, 0, v_lastReduction_2861_);
v___x_2899_ = v___x_2892_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_lastReduction_2861_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
else
{
lean_object* v___x_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; 
lean_del_object(v___x_2892_);
v___x_2901_ = l_Lean_mkAppRev(v_f_2862_, v_rargs_2863_);
lean_dec_ref(v_rargs_2863_);
v___x_2902_ = 0;
v___x_2903_ = l_Lean_Meta_unfoldDefinition_x3f(v___x_2901_, v___x_2902_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2917_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2917_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2917_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
if (lean_obj_tag(v_a_2904_) == 0)
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v_lastReduction_2861_);
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_lastReduction_2861_);
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
lean_object* v_val_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_del_object(v___x_2906_);
v_val_2911_ = lean_ctor_get(v_a_2904_, 0);
lean_inc(v_val_2911_);
lean_dec_ref_known(v_a_2904_, 1);
v___x_2912_ = l_Lean_Expr_getAppFn(v_val_2911_);
v___x_2913_ = l_Lean_Expr_getAppNumArgs(v_val_2911_);
v___x_2914_ = lean_mk_empty_array_with_capacity(v___x_2913_);
lean_dec(v___x_2913_);
v___x_2915_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_val_2911_, v___x_2914_);
v_f_2862_ = v___x_2912_;
v_rargs_2863_ = v___x_2915_;
goto _start;
}
}
}
else
{
lean_dec(v_lastReduction_2861_);
return v___x_2903_;
}
}
}
else
{
lean_object* v___x_2919_; 
lean_dec_ref_known(v_val_2890_, 2);
lean_dec_ref_known(v_f_2862_, 2);
lean_dec_ref(v_rargs_2863_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 0);
lean_ctor_set(v___x_2892_, 0, v_lastReduction_2861_);
v___x_2919_ = v___x_2892_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_lastReduction_2861_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
else
{
lean_object* v___x_2922_; 
lean_dec(v_val_2890_);
lean_dec_ref_known(v_f_2862_, 2);
lean_dec_ref(v_rargs_2863_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 0);
lean_ctor_set(v___x_2892_, 0, v_lastReduction_2861_);
v___x_2922_ = v___x_2892_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_lastReduction_2861_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v___x_2925_; 
lean_dec(v___x_2889_);
lean_dec_ref_known(v_f_2862_, 2);
lean_dec_ref(v_rargs_2863_);
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_lastReduction_2861_);
return v___x_2925_;
}
}
case 11:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_Meta_reduceProj_x3f(v_f_2862_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2948_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2948_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2948_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
if (lean_obj_tag(v_a_2927_) == 0)
{
lean_object* v___x_2932_; 
lean_dec_ref(v_rargs_2863_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v_lastReduction_2861_);
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_lastReduction_2861_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
else
{
lean_object* v_val_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2947_; 
lean_del_object(v___x_2929_);
lean_dec(v_lastReduction_2861_);
v_val_2934_ = lean_ctor_get(v_a_2927_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2936_ = v_a_2927_;
v_isShared_2937_ = v_isSharedCheck_2947_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_val_2934_);
lean_dec(v_a_2927_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2947_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = l_Lean_mkAppRev(v_val_2934_, v_rargs_2863_);
lean_dec_ref(v_rargs_2863_);
lean_inc_ref(v___x_2938_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2941_ = l_Lean_Expr_getAppFn(v___x_2938_);
v___x_2942_ = l_Lean_Expr_getAppNumArgs(v___x_2938_);
v___x_2943_ = lean_mk_empty_array_with_capacity(v___x_2942_);
lean_dec(v___x_2942_);
v___x_2944_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2938_, v___x_2943_);
v_lastReduction_2861_ = v___x_2940_;
v_f_2862_ = v___x_2941_;
v_rargs_2863_ = v___x_2944_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v_rargs_2863_);
lean_dec(v_lastReduction_2861_);
return v___x_2926_;
}
}
case 8:
{
lean_object* v_declName_2949_; lean_object* v_type_2950_; lean_object* v_value_2951_; lean_object* v_body_2952_; uint8_t v_nondep_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_declName_2949_ = lean_ctor_get(v_f_2862_, 0);
lean_inc(v_declName_2949_);
v_type_2950_ = lean_ctor_get(v_f_2862_, 1);
lean_inc_ref(v_type_2950_);
v_value_2951_ = lean_ctor_get(v_f_2862_, 2);
lean_inc_ref(v_value_2951_);
v_body_2952_ = lean_ctor_get(v_f_2862_, 3);
lean_inc_ref(v_body_2952_);
v_nondep_2953_ = lean_ctor_get_uint8(v_f_2862_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_f_2862_, 4);
v___x_2954_ = lean_box(0);
v___x_2955_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_2954_, v_body_2952_, v_rargs_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2975_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2975_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2975_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
if (lean_obj_tag(v_a_2956_) == 0)
{
lean_object* v___x_2961_; 
lean_dec_ref(v_value_2951_);
lean_dec_ref(v_type_2950_);
lean_dec(v_declName_2949_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v_lastReduction_2861_);
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_lastReduction_2861_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
else
{
lean_object* v_val_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_lastReduction_2861_);
v_val_2963_ = lean_ctor_get(v_a_2956_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_a_2956_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2965_ = v_a_2956_;
v_isShared_2966_ = v_isSharedCheck_2974_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_val_2963_);
lean_dec(v_a_2956_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2974_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = l_Lean_Expr_letE___override(v_declName_2949_, v_type_2950_, v_value_2951_, v_val_2963_, v_nondep_2953_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v___x_2967_);
v___x_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2971_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2969_);
v___x_2971_ = v___x_2958_;
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
return v___x_2971_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_2951_);
lean_dec_ref(v_type_2950_);
lean_dec(v_declName_2949_);
lean_dec(v_lastReduction_2861_);
return v___x_2955_;
}
}
default: 
{
lean_object* v___x_2976_; 
lean_dec_ref(v_rargs_2863_);
lean_dec_ref(v_f_2862_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_lastReduction_2861_);
return v___x_2976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go___boxed(lean_object* v_lastReduction_2977_, lean_object* v_f_2978_, lean_object* v_rargs_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v_lastReduction_2977_, v_f_2978_, v_rargs_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(lean_object* v_e_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2992_ = lean_box(0);
v___x_2993_ = l_Lean_Expr_getAppFn(v_e_2986_);
v___x_2994_ = l_Lean_Expr_getAppNumArgs(v_e_2986_);
v___x_2995_ = lean_mk_empty_array_with_capacity(v___x_2994_);
lean_dec(v___x_2994_);
v___x_2996_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_2986_, v___x_2995_);
v___x_2997_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_reduceProjBeta_x3f_go(v___x_2992_, v___x_2993_, v___x_2996_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f___boxed(lean_object* v_e_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_Elab_Tactic_Do_reduceProjBeta_x3f(v_e_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
return v_res_3004_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_box(0);
v___x_3006_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
lean_ctor_set(v___x_3007_, 1, v___x_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg(){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___closed__0);
v___x_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg___boxed(lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(lean_object* v_00_u03b1_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___boxed(lean_object* v_00_u03b1_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0(v_00_u03b1_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(lean_object* v_as_3035_, size_t v_sz_3036_, size_t v_i_3037_, lean_object* v_b_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_a_3048_; uint8_t v___x_3052_; 
v___x_3052_ = lean_usize_dec_lt(v_i_3037_, v_sz_3036_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v_b_3038_);
return v___x_3053_;
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v_a_3054_ = lean_array_uget_borrowed(v_as_3035_, v_i_3037_);
lean_inc(v_a_3054_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v_a_3054_);
v___x_3056_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_b_3038_, v___x_3055_);
lean_dec_ref_known(v___x_3055_, 1);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3039_, v___y_3041_, v___y_3043_, v___y_3045_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3059_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_3054_);
v___x_3060_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_a_3054_, v___x_3059_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; 
lean_dec(v_a_3058_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_b_3038_, v_a_3061_);
v_a_3048_ = v___x_3062_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3083_; 
v_a_3063_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3065_ = v___x_3060_;
v_isShared_3066_ = v_isSharedCheck_3083_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3060_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3083_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
uint8_t v___y_3068_; uint8_t v___x_3081_; 
v___x_3081_ = l_Lean_Exception_isInterrupt(v_a_3063_);
if (v___x_3081_ == 0)
{
uint8_t v___x_3082_; 
lean_inc(v_a_3063_);
v___x_3082_ = l_Lean_Exception_isRuntime(v_a_3063_);
v___y_3068_ = v___x_3082_;
goto v___jp_3067_;
}
else
{
v___y_3068_ = v___x_3081_;
goto v___jp_3067_;
}
v___jp_3067_:
{
if (v___y_3068_ == 0)
{
lean_object* v___x_3069_; 
lean_del_object(v___x_3065_);
lean_dec(v_a_3063_);
v___x_3069_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3058_, v___y_3068_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref_known(v___x_3069_, 1);
v_a_3048_ = v_b_3038_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec_ref(v_b_3038_);
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v___x_3079_; 
lean_dec(v_a_3058_);
lean_dec_ref(v_b_3038_);
if (v_isShared_3066_ == 0)
{
v___x_3079_ = v___x_3065_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3063_);
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
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v_b_3038_);
v_a_3084_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3057_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3057_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
v_a_3048_ = v_b_3038_;
goto v___jp_3047_;
}
}
v___jp_3047_:
{
size_t v___x_3049_; size_t v___x_3050_; 
v___x_3049_ = ((size_t)1ULL);
v___x_3050_ = lean_usize_add(v_i_3037_, v___x_3049_);
v_i_3037_ = v___x_3050_;
v_b_3038_ = v_a_3048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg___boxed(lean_object* v_as_3092_, lean_object* v_sz_3093_, lean_object* v_i_3094_, lean_object* v_b_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
size_t v_sz_boxed_3104_; size_t v_i_boxed_3105_; lean_object* v_res_3106_; 
v_sz_boxed_3104_ = lean_unbox_usize(v_sz_3093_);
lean_dec(v_sz_3093_);
v_i_boxed_3105_ = lean_unbox_usize(v_i_3094_);
lean_dec(v_i_3094_);
v_res_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_3092_, v_sz_boxed_3104_, v_i_boxed_3105_, v_b_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v_as_3092_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(lean_object* v_msg_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_ref_3113_; lean_object* v___x_3114_; lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3123_; 
v_ref_3113_ = lean_ctor_get(v___y_3110_, 5);
v___x_3114_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_instEvalExprConfig_evalExpr_spec__1_spec__1(v_msg_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3123_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3123_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
lean_inc(v_ref_3113_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_ref_3113_);
lean_ctor_set(v___x_3119_, 1, v_a_3115_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set_tag(v___x_3117_, 1);
lean_ctor_set(v___x_3117_, 0, v___x_3119_);
v___x_3121_ = v___x_3117_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3119_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg___boxed(lean_object* v_msg_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(lean_object* v_ref_3131_, lean_object* v_msg_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_fileName_3142_; lean_object* v_fileMap_3143_; lean_object* v_options_3144_; lean_object* v_currRecDepth_3145_; lean_object* v_maxRecDepth_3146_; lean_object* v_ref_3147_; lean_object* v_currNamespace_3148_; lean_object* v_openDecls_3149_; lean_object* v_initHeartbeats_3150_; lean_object* v_maxHeartbeats_3151_; lean_object* v_quotContext_3152_; lean_object* v_currMacroScope_3153_; uint8_t v_diag_3154_; lean_object* v_cancelTk_x3f_3155_; uint8_t v_suppressElabErrors_3156_; lean_object* v_inheritedTraceOptions_3157_; lean_object* v_ref_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v_fileName_3142_ = lean_ctor_get(v___y_3139_, 0);
v_fileMap_3143_ = lean_ctor_get(v___y_3139_, 1);
v_options_3144_ = lean_ctor_get(v___y_3139_, 2);
v_currRecDepth_3145_ = lean_ctor_get(v___y_3139_, 3);
v_maxRecDepth_3146_ = lean_ctor_get(v___y_3139_, 4);
v_ref_3147_ = lean_ctor_get(v___y_3139_, 5);
v_currNamespace_3148_ = lean_ctor_get(v___y_3139_, 6);
v_openDecls_3149_ = lean_ctor_get(v___y_3139_, 7);
v_initHeartbeats_3150_ = lean_ctor_get(v___y_3139_, 8);
v_maxHeartbeats_3151_ = lean_ctor_get(v___y_3139_, 9);
v_quotContext_3152_ = lean_ctor_get(v___y_3139_, 10);
v_currMacroScope_3153_ = lean_ctor_get(v___y_3139_, 11);
v_diag_3154_ = lean_ctor_get_uint8(v___y_3139_, sizeof(void*)*14);
v_cancelTk_x3f_3155_ = lean_ctor_get(v___y_3139_, 12);
v_suppressElabErrors_3156_ = lean_ctor_get_uint8(v___y_3139_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3157_ = lean_ctor_get(v___y_3139_, 13);
v_ref_3158_ = l_Lean_replaceRef(v_ref_3131_, v_ref_3147_);
lean_inc_ref(v_inheritedTraceOptions_3157_);
lean_inc(v_cancelTk_x3f_3155_);
lean_inc(v_currMacroScope_3153_);
lean_inc(v_quotContext_3152_);
lean_inc(v_maxHeartbeats_3151_);
lean_inc(v_initHeartbeats_3150_);
lean_inc(v_openDecls_3149_);
lean_inc(v_currNamespace_3148_);
lean_inc(v_maxRecDepth_3146_);
lean_inc(v_currRecDepth_3145_);
lean_inc_ref(v_options_3144_);
lean_inc_ref(v_fileMap_3143_);
lean_inc_ref(v_fileName_3142_);
v___x_3159_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3159_, 0, v_fileName_3142_);
lean_ctor_set(v___x_3159_, 1, v_fileMap_3143_);
lean_ctor_set(v___x_3159_, 2, v_options_3144_);
lean_ctor_set(v___x_3159_, 3, v_currRecDepth_3145_);
lean_ctor_set(v___x_3159_, 4, v_maxRecDepth_3146_);
lean_ctor_set(v___x_3159_, 5, v_ref_3158_);
lean_ctor_set(v___x_3159_, 6, v_currNamespace_3148_);
lean_ctor_set(v___x_3159_, 7, v_openDecls_3149_);
lean_ctor_set(v___x_3159_, 8, v_initHeartbeats_3150_);
lean_ctor_set(v___x_3159_, 9, v_maxHeartbeats_3151_);
lean_ctor_set(v___x_3159_, 10, v_quotContext_3152_);
lean_ctor_set(v___x_3159_, 11, v_currMacroScope_3153_);
lean_ctor_set(v___x_3159_, 12, v_cancelTk_x3f_3155_);
lean_ctor_set(v___x_3159_, 13, v_inheritedTraceOptions_3157_);
lean_ctor_set_uint8(v___x_3159_, sizeof(void*)*14, v_diag_3154_);
lean_ctor_set_uint8(v___x_3159_, sizeof(void*)*14 + 1, v_suppressElabErrors_3156_);
v___x_3160_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_3132_, v___y_3137_, v___y_3138_, v___x_3159_, v___y_3140_);
lean_dec_ref_known(v___x_3159_, 14);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_ref_3161_, lean_object* v_msg_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3161_, v_msg_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v_ref_3161_);
return v_res_3172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__0);
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_3177_ = lean_unsigned_to_nat(0u);
v___x_3178_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
lean_ctor_set(v___x_3178_, 2, v___x_3177_);
lean_ctor_set(v___x_3178_, 3, v___x_3177_);
lean_ctor_set(v___x_3178_, 4, v___x_3176_);
lean_ctor_set(v___x_3178_, 5, v___x_3176_);
lean_ctor_set(v___x_3178_, 6, v___x_3176_);
lean_ctor_set(v___x_3178_, 7, v___x_3176_);
lean_ctor_set(v___x_3178_, 8, v___x_3176_);
lean_ctor_set(v___x_3178_, 9, v___x_3176_);
lean_ctor_set(v___x_3178_, 10, v___x_3176_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = lean_unsigned_to_nat(32u);
v___x_3180_ = lean_mk_empty_array_with_capacity(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3182_ = ((size_t)5ULL);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = lean_unsigned_to_nat(32u);
v___x_3185_ = lean_mk_empty_array_with_capacity(v___x_3184_);
v___x_3186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__3);
v___x_3187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___x_3185_);
lean_ctor_set(v___x_3187_, 2, v___x_3183_);
lean_ctor_set(v___x_3187_, 3, v___x_3183_);
lean_ctor_set_usize(v___x_3187_, 4, v___x_3182_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3188_ = lean_box(1);
v___x_3189_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__4);
v___x_3190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__1);
v___x_3191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v___x_3189_);
lean_ctor_set(v___x_3191_, 2, v___x_3188_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__6));
v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__8));
v___x_3197_ = l_Lean_stringToMessageData(v___x_3196_);
return v___x_3197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__10));
v___x_3200_ = l_Lean_stringToMessageData(v___x_3199_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__12));
v___x_3203_ = l_Lean_stringToMessageData(v___x_3202_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__14));
v___x_3206_ = l_Lean_stringToMessageData(v___x_3205_);
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__16));
v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__18));
v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object* v_msg_3213_, lean_object* v_declHint_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; lean_object* v_env_3218_; uint8_t v___x_3219_; 
v___x_3217_ = lean_st_ref_get(v___y_3215_);
v_env_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc_ref(v_env_3218_);
lean_dec(v___x_3217_);
v___x_3219_ = l_Lean_Name_isAnonymous(v_declHint_3214_);
if (v___x_3219_ == 0)
{
uint8_t v_isExporting_3220_; 
v_isExporting_3220_ = lean_ctor_get_uint8(v_env_3218_, sizeof(void*)*8);
if (v_isExporting_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec_ref(v_env_3218_);
lean_dec(v_declHint_3214_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_msg_3213_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; uint8_t v___x_3223_; 
lean_inc_ref(v_env_3218_);
v___x_3222_ = l_Lean_Environment_setExporting(v_env_3218_, v___x_3219_);
lean_inc(v_declHint_3214_);
lean_inc_ref(v___x_3222_);
v___x_3223_ = l_Lean_Environment_contains(v___x_3222_, v_declHint_3214_, v_isExporting_3220_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_dec_ref(v___x_3222_);
lean_dec_ref(v_env_3218_);
lean_dec(v_declHint_3214_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_msg_3213_);
return v___x_3224_;
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v_c_3230_; lean_object* v___x_3231_; 
v___x_3225_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__2);
v___x_3226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__5);
v___x_3227_ = l_Lean_Options_empty;
v___x_3228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3222_);
lean_ctor_set(v___x_3228_, 1, v___x_3225_);
lean_ctor_set(v___x_3228_, 2, v___x_3226_);
lean_ctor_set(v___x_3228_, 3, v___x_3227_);
lean_inc(v_declHint_3214_);
v___x_3229_ = l_Lean_MessageData_ofConstName(v_declHint_3214_, v___x_3219_);
v_c_3230_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3230_, 0, v___x_3228_);
lean_ctor_set(v_c_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3218_, v_declHint_3214_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec_ref(v_env_3218_);
lean_dec(v_declHint_3214_);
v___x_3232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_3233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_ctor_set(v___x_3233_, 1, v_c_3230_);
v___x_3234_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__9);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Lean_MessageData_note(v___x_3235_);
v___x_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3237_, 0, v_msg_3213_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
else
{
lean_object* v_val_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3274_; 
v_val_3239_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3241_ = v___x_3231_;
v_isShared_3242_ = v_isSharedCheck_3274_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_val_3239_);
lean_dec(v___x_3231_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3274_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v_mod_3246_; uint8_t v___x_3247_; 
v___x_3243_ = lean_box(0);
v___x_3244_ = l_Lean_Environment_header(v_env_3218_);
lean_dec_ref(v_env_3218_);
v___x_3245_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3244_);
v_mod_3246_ = lean_array_get(v___x_3243_, v___x_3245_, v_val_3239_);
lean_dec(v_val_3239_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = l_Lean_isPrivateName(v_declHint_3214_);
lean_dec(v_declHint_3214_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v___x_3248_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__11);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v_c_3230_);
v___x_3250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__13);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_MessageData_ofName(v_mod_3246_);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__15);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = l_Lean_MessageData_note(v___x_3255_);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v_msg_3213_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set_tag(v___x_3241_, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3257_);
v___x_3259_ = v___x_3241_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3261_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__7);
v___x_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v_c_3230_);
v___x_3263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__17);
v___x_3264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = l_Lean_MessageData_ofName(v_mod_3246_);
v___x_3266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___closed__19);
v___x_3268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = l_Lean_MessageData_note(v___x_3268_);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_msg_3213_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set_tag(v___x_3241_, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3270_);
v___x_3272_ = v___x_3241_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3275_; 
lean_dec_ref(v_env_3218_);
lean_dec(v_declHint_3214_);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_msg_3213_);
return v___x_3275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_msg_3276_, lean_object* v_declHint_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3276_, v_declHint_3277_, v___y_3278_);
lean_dec(v___y_3278_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(lean_object* v_msg_3281_, lean_object* v_declHint_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3302_; 
v___x_3292_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_3281_, v_declHint_3282_, v___y_3290_);
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3297_ = l_Lean_unknownIdentifierMessageTag;
v___x_3298_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v_a_3293_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3298_);
v___x_3300_ = v___x_3295_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_msg_3303_, lean_object* v_declHint_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_3303_, v_declHint_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(lean_object* v_ref_3315_, lean_object* v_msg_3316_, lean_object* v_declHint_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v___x_3327_; lean_object* v_a_3328_; lean_object* v___x_3329_; 
v___x_3327_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7(v_msg_3316_, v_declHint_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref(v___x_3327_);
v___x_3329_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_3315_, v_a_3328_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_ref_3330_, lean_object* v_msg_3331_, lean_object* v_declHint_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3330_, v_msg_3331_, v_declHint_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v_ref_3330_);
return v_res_3342_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__0));
v___x_3345_ = l_Lean_stringToMessageData(v___x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(lean_object* v_ref_3346_, lean_object* v_constName_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3357_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___closed__1);
v___x_3358_ = 0;
lean_inc(v_constName_3347_);
v___x_3359_ = l_Lean_MessageData_ofConstName(v_constName_3347_, v___x_3358_);
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3357_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_3346_, v___x_3362_, v_constName_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg___boxed(lean_object* v_ref_3364_, lean_object* v_constName_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3364_, v_constName_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v_ref_3364_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(lean_object* v_constName_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_ref_3386_; lean_object* v___x_3387_; 
v_ref_3386_ = lean_ctor_get(v___y_3383_, 5);
v___x_3387_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_3386_, v_constName_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg___boxed(lean_object* v_constName_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(lean_object* v_fst_3399_, lean_object* v_fst_3400_, lean_object* v_specThm_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_proof_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_proof_3411_ = lean_ctor_get(v_specThm_3401_, 2);
lean_inc_ref(v_proof_3411_);
lean_dec_ref(v_specThm_3401_);
v___x_3412_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(v_fst_3399_, v_proof_3411_);
v___x_3413_ = lean_box(0);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v_fst_3400_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0___boxed(lean_object* v_fst_3417_, lean_object* v_fst_3418_, lean_object* v_specThm_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3417_, v_fst_3418_, v_specThm_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(lean_object* v_constName_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; lean_object* v_env_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; 
v___x_3440_ = lean_st_ref_get(v___y_3438_);
v_env_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc_ref(v_env_3441_);
lean_dec(v___x_3440_);
v___x_3442_ = 0;
lean_inc(v_constName_3430_);
v___x_3443_ = l_Lean_Environment_find_x3f(v_env_3441_, v_constName_3430_, v___x_3442_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
return v___x_3444_;
}
else
{
lean_object* v_val_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_constName_3430_);
v_val_3445_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3443_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_val_3445_);
lean_dec(v___x_3443_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set_tag(v___x_3447_, 0);
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_val_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2___boxed(lean_object* v_constName_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_constName_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
return v_res_3463_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__7));
v___x_3485_ = l_Lean_stringToMessageData(v___x_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(lean_object* v_as_3487_, size_t v_sz_3488_, size_t v_i_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_a_3501_; uint8_t v_starArg_3505_; 
v_starArg_3505_ = lean_usize_dec_lt(v_i_3489_, v_sz_3488_);
if (v_starArg_3505_ == 0)
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_b_3490_);
return v___x_3506_;
}
else
{
lean_object* v_snd_3507_; lean_object* v_fst_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3828_; 
v_snd_3507_ = lean_ctor_get(v_b_3490_, 1);
v_fst_3508_ = lean_ctor_get(v_b_3490_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_b_3490_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3510_ = v_b_3490_;
v_isShared_3511_ = v_isSharedCheck_3828_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_snd_3507_);
lean_inc(v_fst_3508_);
lean_dec(v_b_3490_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3828_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v_fst_3512_; lean_object* v_snd_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3827_; 
v_fst_3512_ = lean_ctor_get(v_snd_3507_, 0);
v_snd_3513_ = lean_ctor_get(v_snd_3507_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_snd_3507_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3515_ = v_snd_3507_;
v_isShared_3516_ = v_isSharedCheck_3827_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_snd_3513_);
lean_inc(v_fst_3512_);
lean_dec(v_snd_3507_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3827_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_fst_3518_; lean_object* v_snd_3519_; lean_object* v_fst_3527_; lean_object* v_snd_3528_; lean_object* v_fst_3532_; lean_object* v_snd_3533_; lean_object* v___x_3536_; lean_object* v_a_3537_; lean_object* v___y_3543_; lean_object* v___y_3544_; uint8_t v___y_3545_; lean_object* v___y_3558_; lean_object* v___y_3559_; uint8_t v___y_3560_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3536_ = lean_unsigned_to_nat(1u);
v_a_3537_ = lean_array_uget_borrowed(v_as_3487_, v_i_3489_);
lean_inc(v_a_3537_);
v___x_3572_ = l_Lean_Syntax_getKind(v_a_3537_);
v___x_3573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__2));
v___x_3574_ = lean_name_eq(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__4));
v___x_3576_ = lean_name_eq(v___x_3572_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; uint8_t v___x_3578_; 
lean_del_object(v___x_3515_);
lean_del_object(v___x_3510_);
v___x_3577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__6));
v___x_3578_ = lean_name_eq(v___x_3572_, v___x_3577_);
lean_dec(v___x_3572_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__0___redArg();
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec_ref_known(v___x_3579_, 1);
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v_fst_3512_);
lean_ctor_set(v___x_3580_, 1, v_snd_3513_);
v___x_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3581_, 0, v_fst_3508_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v_a_3501_ = v___x_3581_;
goto v___jp_3500_;
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3582_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3579_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3579_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec(v_snd_3513_);
lean_inc(v_a_3537_);
v___x_3590_ = lean_array_push(v_fst_3512_, v_a_3537_);
v___x_3591_ = lean_box(v_starArg_3505_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v_fst_3508_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v_a_3501_ = v___x_3593_;
goto v___jp_3500_;
}
}
else
{
lean_object* v___x_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
lean_dec(v___x_3572_);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = l_Lean_Syntax_getArg(v_a_3537_, v___x_3594_);
v___x_3596_ = l_Lean_Syntax_isNone(v___x_3595_);
lean_dec(v___x_3595_);
if (v___x_3596_ == 0)
{
lean_del_object(v___x_3515_);
lean_del_object(v___x_3510_);
goto v___jp_3538_;
}
else
{
lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3597_ = l_Lean_Syntax_getArg(v_a_3537_, v___x_3536_);
v___x_3598_ = l_Lean_Syntax_isNone(v___x_3597_);
lean_dec(v___x_3597_);
if (v___x_3598_ == 0)
{
lean_del_object(v___x_3515_);
lean_del_object(v___x_3510_);
goto v___jp_3538_;
}
else
{
lean_object* v___x_3599_; 
v___x_3599_ = l_Lean_Meta_saveState___redArg(v___y_3496_, v___y_3498_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3643_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = lean_unsigned_to_nat(2u);
v___x_3602_ = l_Lean_Syntax_getArg(v_a_3537_, v___x_3601_);
v___x_3708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__9));
lean_inc(v___x_3602_);
v___x_3709_ = l_Lean_Elab_Term_resolveId_x3f(v___x_3602_, v___x_3708_, v_starArg_3505_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_dec(v_a_3600_);
v___y_3643_ = v___x_3709_;
goto v___jp_3642_;
}
else
{
lean_object* v_a_3710_; uint8_t v___y_3712_; uint8_t v___x_3723_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
v___x_3723_ = l_Lean_Exception_isInterrupt(v_a_3710_);
if (v___x_3723_ == 0)
{
uint8_t v___x_3724_; 
v___x_3724_ = l_Lean_Exception_isRuntime(v_a_3710_);
v___y_3712_ = v___x_3724_;
goto v___jp_3711_;
}
else
{
lean_dec(v_a_3710_);
v___y_3712_ = v___x_3723_;
goto v___jp_3711_;
}
v___jp_3711_:
{
if (v___y_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_dec_ref_known(v___x_3709_, 1);
v___x_3713_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3600_, v___y_3496_, v___y_3498_);
lean_dec(v_a_3600_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v___x_3714_; 
lean_dec_ref_known(v___x_3713_, 1);
lean_inc(v___x_3602_);
v___x_3714_ = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(v___x_3602_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
v___y_3643_ = v___x_3714_;
goto v___jp_3642_;
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v___x_3602_);
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
v_a_3715_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3713_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3713_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_dec(v_a_3600_);
v___y_3643_ = v___x_3709_;
goto v___jp_3642_;
}
}
}
v___jp_3603_:
{
lean_object* v_fileName_3608_; lean_object* v_fileMap_3609_; lean_object* v_options_3610_; lean_object* v_currRecDepth_3611_; lean_object* v_maxRecDepth_3612_; lean_object* v_ref_3613_; lean_object* v_currNamespace_3614_; lean_object* v_openDecls_3615_; lean_object* v_initHeartbeats_3616_; lean_object* v_maxHeartbeats_3617_; lean_object* v_quotContext_3618_; lean_object* v_currMacroScope_3619_; uint8_t v_diag_3620_; lean_object* v_cancelTk_x3f_3621_; uint8_t v_suppressElabErrors_3622_; lean_object* v_inheritedTraceOptions_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v_ref_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v_fileName_3608_ = lean_ctor_get(v___y_3606_, 0);
v_fileMap_3609_ = lean_ctor_get(v___y_3606_, 1);
v_options_3610_ = lean_ctor_get(v___y_3606_, 2);
v_currRecDepth_3611_ = lean_ctor_get(v___y_3606_, 3);
v_maxRecDepth_3612_ = lean_ctor_get(v___y_3606_, 4);
v_ref_3613_ = lean_ctor_get(v___y_3606_, 5);
v_currNamespace_3614_ = lean_ctor_get(v___y_3606_, 6);
v_openDecls_3615_ = lean_ctor_get(v___y_3606_, 7);
v_initHeartbeats_3616_ = lean_ctor_get(v___y_3606_, 8);
v_maxHeartbeats_3617_ = lean_ctor_get(v___y_3606_, 9);
v_quotContext_3618_ = lean_ctor_get(v___y_3606_, 10);
v_currMacroScope_3619_ = lean_ctor_get(v___y_3606_, 11);
v_diag_3620_ = lean_ctor_get_uint8(v___y_3606_, sizeof(void*)*14);
v_cancelTk_x3f_3621_ = lean_ctor_get(v___y_3606_, 12);
v_suppressElabErrors_3622_ = lean_ctor_get_uint8(v___y_3606_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3623_ = lean_ctor_get(v___y_3606_, 13);
v___x_3624_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___closed__8);
lean_inc(v___x_3602_);
v___x_3625_ = l_Lean_MessageData_ofSyntax(v___x_3602_);
v___x_3626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3624_);
lean_ctor_set(v___x_3626_, 1, v___x_3625_);
v___x_3627_ = lean_obj_once(&l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5, &l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5_once, _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_elabConfig_evalConfigItem_spec__0_spec__0___closed__5);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3626_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
v_ref_3629_ = l_Lean_replaceRef(v___x_3602_, v_ref_3613_);
lean_dec(v___x_3602_);
lean_inc_ref(v_inheritedTraceOptions_3623_);
lean_inc(v_cancelTk_x3f_3621_);
lean_inc(v_currMacroScope_3619_);
lean_inc(v_quotContext_3618_);
lean_inc(v_maxHeartbeats_3617_);
lean_inc(v_initHeartbeats_3616_);
lean_inc(v_openDecls_3615_);
lean_inc(v_currNamespace_3614_);
lean_inc(v_maxRecDepth_3612_);
lean_inc(v_currRecDepth_3611_);
lean_inc_ref(v_options_3610_);
lean_inc_ref(v_fileMap_3609_);
lean_inc_ref(v_fileName_3608_);
v___x_3630_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3630_, 0, v_fileName_3608_);
lean_ctor_set(v___x_3630_, 1, v_fileMap_3609_);
lean_ctor_set(v___x_3630_, 2, v_options_3610_);
lean_ctor_set(v___x_3630_, 3, v_currRecDepth_3611_);
lean_ctor_set(v___x_3630_, 4, v_maxRecDepth_3612_);
lean_ctor_set(v___x_3630_, 5, v_ref_3629_);
lean_ctor_set(v___x_3630_, 6, v_currNamespace_3614_);
lean_ctor_set(v___x_3630_, 7, v_openDecls_3615_);
lean_ctor_set(v___x_3630_, 8, v_initHeartbeats_3616_);
lean_ctor_set(v___x_3630_, 9, v_maxHeartbeats_3617_);
lean_ctor_set(v___x_3630_, 10, v_quotContext_3618_);
lean_ctor_set(v___x_3630_, 11, v_currMacroScope_3619_);
lean_ctor_set(v___x_3630_, 12, v_cancelTk_x3f_3621_);
lean_ctor_set(v___x_3630_, 13, v_inheritedTraceOptions_3623_);
lean_ctor_set_uint8(v___x_3630_, sizeof(void*)*14, v_diag_3620_);
lean_ctor_set_uint8(v___x_3630_, sizeof(void*)*14 + 1, v_suppressElabErrors_3622_);
v___x_3631_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v___x_3628_, v___y_3604_, v___y_3605_, v___x_3630_, v___y_3607_);
lean_dec_ref_known(v___x_3630_, 14);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_dec_ref_known(v___x_3631_, 1);
v___x_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3632_, 0, v_fst_3512_);
lean_ctor_set(v___x_3632_, 1, v_snd_3513_);
v___x_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3633_, 0, v_fst_3508_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v_a_3501_ = v___x_3633_;
goto v___jp_3500_;
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3634_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3631_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3631_);
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
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
v___jp_3642_:
{
if (lean_obj_tag(v___y_3643_) == 0)
{
lean_object* v_a_3644_; 
v_a_3644_ = lean_ctor_get(v___y_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___y_3643_, 1);
if (lean_obj_tag(v_a_3644_) == 1)
{
lean_object* v_val_3645_; 
v_val_3645_ = lean_ctor_get(v_a_3644_, 0);
lean_inc(v_val_3645_);
lean_dec_ref_known(v_a_3644_, 1);
switch(lean_obj_tag(v_val_3645_))
{
case 4:
{
lean_object* v_declName_3646_; lean_object* v___x_3647_; 
lean_dec(v___x_3602_);
lean_del_object(v___x_3515_);
lean_del_object(v___x_3510_);
v_declName_3646_ = lean_ctor_get(v_val_3645_, 0);
lean_inc_n(v_declName_3646_, 2);
lean_dec_ref_known(v_val_3645_, 2);
v___x_3647_ = l_Lean_getConstInfo___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__2(v_declName_3646_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v___x_3648_; 
lean_dec_ref_known(v___x_3647_, 1);
v___x_3648_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3492_, v___y_3494_, v___y_3496_, v___y_3498_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
v___x_3650_ = lean_unsigned_to_nat(1000u);
v___x_3651_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_3646_, v___x_3650_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3653_; 
lean_dec(v_a_3649_);
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_3508_, v_a_3652_);
v_fst_3527_ = v___x_3653_;
v_snd_3528_ = v_fst_3512_;
goto v___jp_3526_;
}
else
{
lean_object* v_a_3654_; uint8_t v___x_3655_; 
v_a_3654_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3655_ = l_Lean_Exception_isInterrupt(v_a_3654_);
if (v___x_3655_ == 0)
{
uint8_t v___x_3656_; 
lean_inc(v_a_3654_);
v___x_3656_ = l_Lean_Exception_isRuntime(v_a_3654_);
v___y_3543_ = v_a_3649_;
v___y_3544_ = v_a_3654_;
v___y_3545_ = v___x_3656_;
goto v___jp_3542_;
}
else
{
v___y_3543_ = v_a_3649_;
v___y_3544_ = v_a_3654_;
v___y_3545_ = v___x_3655_;
goto v___jp_3542_;
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec(v_declName_3646_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3657_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3648_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3648_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec(v_declName_3646_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3665_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3647_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3647_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_3673_; lean_object* v___x_3674_; 
lean_dec(v___x_3602_);
v_fvarId_3673_ = lean_ctor_get(v_val_3645_, 0);
lean_inc(v_fvarId_3673_);
v___x_3674_ = l_Lean_Meta_getFVarLocalDecl___redArg(v_val_3645_, v___y_3495_, v___y_3497_, v___y_3498_);
lean_dec_ref_known(v_val_3645_, 1);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v___x_3675_; 
lean_dec_ref_known(v___x_3674_, 1);
v___x_3675_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3492_, v___y_3494_, v___y_3496_, v___y_3498_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3676_);
lean_dec_ref_known(v___x_3675_, 1);
v___x_3677_ = lean_unsigned_to_nat(1000u);
v___x_3678_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvarId_3673_, v___x_3677_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; 
lean_dec(v_a_3676_);
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3680_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_3508_, v_a_3679_);
v_fst_3518_ = v___x_3680_;
v_snd_3519_ = v_fst_3512_;
goto v___jp_3517_;
}
else
{
lean_object* v_a_3681_; uint8_t v___x_3682_; 
v_a_3681_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3682_ = l_Lean_Exception_isInterrupt(v_a_3681_);
if (v___x_3682_ == 0)
{
uint8_t v___x_3683_; 
lean_inc(v_a_3681_);
v___x_3683_ = l_Lean_Exception_isRuntime(v_a_3681_);
v___y_3558_ = v_a_3681_;
v___y_3559_ = v_a_3676_;
v___y_3560_ = v___x_3683_;
goto v___jp_3557_;
}
else
{
v___y_3558_ = v_a_3681_;
v___y_3559_ = v_a_3676_;
v___y_3560_ = v___x_3682_;
goto v___jp_3557_;
}
}
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec(v_fvarId_3673_);
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
v_a_3684_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3675_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3675_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_fvarId_3673_);
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
v_a_3692_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3674_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3674_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
default: 
{
lean_dec(v_val_3645_);
lean_del_object(v___x_3515_);
lean_del_object(v___x_3510_);
v___y_3604_ = v___y_3495_;
v___y_3605_ = v___y_3496_;
v___y_3606_ = v___y_3497_;
v___y_3607_ = v___y_3498_;
goto v___jp_3603_;
}
}
}
else
{
lean_dec(v_a_3644_);
lean_del_object(v___x_3515_);
lean_del_object(v___x_3510_);
v___y_3604_ = v___y_3495_;
v___y_3605_ = v___y_3496_;
v___y_3606_ = v___y_3497_;
v___y_3607_ = v___y_3498_;
goto v___jp_3603_;
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v___x_3602_);
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
v_a_3700_ = lean_ctor_get(v___y_3643_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___y_3643_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___y_3643_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___y_3643_);
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
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
v_a_3725_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3599_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3599_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3733_; 
lean_dec(v___x_3572_);
lean_del_object(v___x_3515_);
lean_del_object(v___x_3510_);
v___x_3733_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3492_, v___y_3494_, v___y_3496_, v___y_3498_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3818_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3818_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3818_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___y_3739_; uint8_t v___y_3740_; lean_object* v_a_3755_; lean_object* v___y_3759_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = l_Lean_Syntax_getArg(v_a_3537_, v___x_3536_);
lean_inc(v___x_3765_);
v___x_3766_ = l_Lean_Elab_Term_isLocalIdent_x3f(v___x_3765_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
if (lean_obj_tag(v_a_3767_) == 1)
{
lean_object* v_val_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
lean_dec(v___x_3765_);
v_val_3768_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_val_3768_);
lean_dec_ref_known(v_a_3767_, 1);
v___x_3769_ = l_Lean_Expr_fvarId_x21(v_val_3768_);
lean_dec(v_val_3768_);
v___x_3770_ = lean_unsigned_to_nat(1000u);
v___x_3771_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_3769_, v___x_3770_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3773_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
lean_inc(v_fst_3512_);
lean_inc(v_fst_3508_);
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3508_, v_fst_3512_, v_a_3772_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
v___y_3759_ = v___x_3773_;
goto v___jp_3758_;
}
else
{
lean_object* v_a_3774_; 
v_a_3774_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3771_, 1);
v_a_3755_ = v_a_3774_;
goto v___jp_3754_;
}
}
else
{
lean_object* v___x_3775_; 
lean_dec(v_a_3767_);
v___x_3775_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3492_, v___y_3494_, v___y_3496_, v___y_3498_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___x_3775_, 1);
v___x_3777_ = lean_box(0);
lean_inc(v___x_3765_);
v___x_3778_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_3765_, v___x_3777_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_dec(v_a_3776_);
lean_dec(v___x_3765_);
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3778_, 1);
v___x_3780_ = lean_unsigned_to_nat(1000u);
v___x_3781_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_a_3779_, v___x_3780_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
lean_inc(v_fst_3512_);
lean_inc(v_fst_3508_);
v___x_3783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3508_, v_fst_3512_, v_a_3782_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
v___y_3759_ = v___x_3783_;
goto v___jp_3758_;
}
else
{
lean_object* v_a_3784_; 
v_a_3784_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3781_, 1);
v_a_3755_ = v_a_3784_;
goto v___jp_3754_;
}
}
else
{
lean_object* v_a_3785_; uint8_t v___y_3787_; uint8_t v___x_3814_; 
v_a_3785_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3778_, 1);
v___x_3814_ = l_Lean_Exception_isInterrupt(v_a_3785_);
if (v___x_3814_ == 0)
{
uint8_t v___x_3815_; 
lean_inc(v_a_3785_);
v___x_3815_ = l_Lean_Exception_isRuntime(v_a_3785_);
v___y_3787_ = v___x_3815_;
goto v___jp_3786_;
}
else
{
v___y_3787_ = v___x_3814_;
goto v___jp_3786_;
}
v___jp_3786_:
{
if (v___y_3787_ == 0)
{
lean_object* v___x_3788_; 
lean_dec(v_a_3785_);
v___x_3788_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3776_, v___y_3787_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_fileName_3789_; lean_object* v_fileMap_3790_; lean_object* v_options_3791_; lean_object* v_currRecDepth_3792_; lean_object* v_maxRecDepth_3793_; lean_object* v_ref_3794_; lean_object* v_currNamespace_3795_; lean_object* v_openDecls_3796_; lean_object* v_initHeartbeats_3797_; lean_object* v_maxHeartbeats_3798_; lean_object* v_quotContext_3799_; lean_object* v_currMacroScope_3800_; uint8_t v_diag_3801_; lean_object* v_cancelTk_x3f_3802_; uint8_t v_suppressElabErrors_3803_; lean_object* v_inheritedTraceOptions_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v_ref_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_dec_ref_known(v___x_3788_, 1);
v_fileName_3789_ = lean_ctor_get(v___y_3497_, 0);
v_fileMap_3790_ = lean_ctor_get(v___y_3497_, 1);
v_options_3791_ = lean_ctor_get(v___y_3497_, 2);
v_currRecDepth_3792_ = lean_ctor_get(v___y_3497_, 3);
v_maxRecDepth_3793_ = lean_ctor_get(v___y_3497_, 4);
v_ref_3794_ = lean_ctor_get(v___y_3497_, 5);
v_currNamespace_3795_ = lean_ctor_get(v___y_3497_, 6);
v_openDecls_3796_ = lean_ctor_get(v___y_3497_, 7);
v_initHeartbeats_3797_ = lean_ctor_get(v___y_3497_, 8);
v_maxHeartbeats_3798_ = lean_ctor_get(v___y_3497_, 9);
v_quotContext_3799_ = lean_ctor_get(v___y_3497_, 10);
v_currMacroScope_3800_ = lean_ctor_get(v___y_3497_, 11);
v_diag_3801_ = lean_ctor_get_uint8(v___y_3497_, sizeof(void*)*14);
v_cancelTk_x3f_3802_ = lean_ctor_get(v___y_3497_, 12);
v_suppressElabErrors_3803_ = lean_ctor_get_uint8(v___y_3497_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3804_ = lean_ctor_get(v___y_3497_, 13);
v___x_3805_ = l_Lean_Syntax_getId(v___x_3765_);
v___x_3806_ = l_Lean_Name_eraseMacroScopes(v___x_3805_);
lean_dec(v___x_3805_);
v_ref_3807_ = l_Lean_replaceRef(v___x_3765_, v_ref_3794_);
lean_dec(v___x_3765_);
lean_inc_ref(v_inheritedTraceOptions_3804_);
lean_inc(v_cancelTk_x3f_3802_);
lean_inc(v_currMacroScope_3800_);
lean_inc(v_quotContext_3799_);
lean_inc(v_maxHeartbeats_3798_);
lean_inc(v_initHeartbeats_3797_);
lean_inc(v_openDecls_3796_);
lean_inc(v_currNamespace_3795_);
lean_inc(v_maxRecDepth_3793_);
lean_inc(v_currRecDepth_3792_);
lean_inc_ref(v_options_3791_);
lean_inc_ref(v_fileMap_3790_);
lean_inc_ref(v_fileName_3789_);
v___x_3808_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3808_, 0, v_fileName_3789_);
lean_ctor_set(v___x_3808_, 1, v_fileMap_3790_);
lean_ctor_set(v___x_3808_, 2, v_options_3791_);
lean_ctor_set(v___x_3808_, 3, v_currRecDepth_3792_);
lean_ctor_set(v___x_3808_, 4, v_maxRecDepth_3793_);
lean_ctor_set(v___x_3808_, 5, v_ref_3807_);
lean_ctor_set(v___x_3808_, 6, v_currNamespace_3795_);
lean_ctor_set(v___x_3808_, 7, v_openDecls_3796_);
lean_ctor_set(v___x_3808_, 8, v_initHeartbeats_3797_);
lean_ctor_set(v___x_3808_, 9, v_maxHeartbeats_3798_);
lean_ctor_set(v___x_3808_, 10, v_quotContext_3799_);
lean_ctor_set(v___x_3808_, 11, v_currMacroScope_3800_);
lean_ctor_set(v___x_3808_, 12, v_cancelTk_x3f_3802_);
lean_ctor_set(v___x_3808_, 13, v_inheritedTraceOptions_3804_);
lean_ctor_set_uint8(v___x_3808_, sizeof(void*)*14, v_diag_3801_);
lean_ctor_set_uint8(v___x_3808_, sizeof(void*)*14 + 1, v_suppressElabErrors_3803_);
v___x_3809_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v___x_3806_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___x_3808_, v___y_3498_);
lean_dec_ref_known(v___x_3808_, 14);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
lean_inc(v_fst_3512_);
lean_inc(v_fst_3508_);
v___x_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___lam__0(v_fst_3508_, v_fst_3512_, v_a_3810_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
v___y_3759_ = v___x_3811_;
goto v___jp_3758_;
}
else
{
lean_object* v_a_3812_; 
v_a_3812_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3809_, 1);
v_a_3755_ = v_a_3812_;
goto v___jp_3754_;
}
}
else
{
lean_object* v_a_3813_; 
lean_dec(v___x_3765_);
v_a_3813_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3788_, 1);
v_a_3755_ = v_a_3813_;
goto v___jp_3754_;
}
}
else
{
lean_dec(v_a_3776_);
lean_dec(v___x_3765_);
v_a_3755_ = v_a_3785_;
goto v___jp_3754_;
}
}
}
}
else
{
lean_object* v_a_3816_; 
lean_dec(v___x_3765_);
v_a_3816_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3775_, 1);
v_a_3755_ = v_a_3816_;
goto v___jp_3754_;
}
}
}
else
{
lean_object* v_a_3817_; 
lean_dec(v___x_3765_);
v_a_3817_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3766_, 1);
v_a_3755_ = v_a_3817_;
goto v___jp_3754_;
}
v___jp_3738_:
{
if (v___y_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec_ref(v___y_3739_);
lean_del_object(v___x_3736_);
v___x_3741_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3734_, v___y_3740_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref_known(v___x_3741_, 1);
lean_inc(v_a_3537_);
v___x_3742_ = lean_array_push(v_fst_3512_, v_a_3537_);
v_fst_3532_ = v_fst_3508_;
v_snd_3533_ = v___x_3742_;
goto v___jp_3531_;
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3743_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3741_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3741_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v___x_3752_; 
lean_dec(v_a_3734_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 1);
lean_ctor_set(v___x_3736_, 0, v___y_3739_);
v___x_3752_ = v___x_3736_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___y_3739_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
v___jp_3754_:
{
uint8_t v___x_3756_; 
v___x_3756_ = l_Lean_Exception_isInterrupt(v_a_3755_);
if (v___x_3756_ == 0)
{
uint8_t v___x_3757_; 
lean_inc_ref(v_a_3755_);
v___x_3757_ = l_Lean_Exception_isRuntime(v_a_3755_);
v___y_3739_ = v_a_3755_;
v___y_3740_ = v___x_3757_;
goto v___jp_3738_;
}
else
{
v___y_3739_ = v_a_3755_;
v___y_3740_ = v___x_3756_;
goto v___jp_3738_;
}
}
v___jp_3758_:
{
if (lean_obj_tag(v___y_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v_snd_3761_; lean_object* v_fst_3762_; lean_object* v_snd_3763_; 
lean_del_object(v___x_3736_);
lean_dec(v_a_3734_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3760_ = lean_ctor_get(v___y_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___y_3759_, 1);
v_snd_3761_ = lean_ctor_get(v_a_3760_, 1);
lean_inc(v_snd_3761_);
lean_dec(v_a_3760_);
v_fst_3762_ = lean_ctor_get(v_snd_3761_, 0);
lean_inc(v_fst_3762_);
v_snd_3763_ = lean_ctor_get(v_snd_3761_, 1);
lean_inc(v_snd_3763_);
lean_dec(v_snd_3761_);
v_fst_3532_ = v_fst_3762_;
v_snd_3533_ = v_snd_3763_;
goto v___jp_3531_;
}
else
{
lean_object* v_a_3764_; 
v_a_3764_ = lean_ctor_get(v___y_3759_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___y_3759_, 1);
v_a_3755_ = v_a_3764_;
goto v___jp_3754_;
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3819_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3733_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3733_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
v___jp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v_snd_3519_);
v___x_3521_ = v___x_3515_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_snd_3519_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_snd_3513_);
v___x_3521_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3521_);
lean_ctor_set(v___x_3510_, 0, v_fst_3518_);
v___x_3523_ = v___x_3510_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_fst_3518_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
v_a_3501_ = v___x_3523_;
goto v___jp_3500_;
}
}
}
v___jp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_snd_3528_);
lean_ctor_set(v___x_3529_, 1, v_snd_3513_);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v_fst_3527_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v_a_3501_ = v___x_3530_;
goto v___jp_3500_;
}
v___jp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3534_, 0, v_snd_3533_);
lean_ctor_set(v___x_3534_, 1, v_snd_3513_);
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v_fst_3532_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v_a_3501_ = v___x_3535_;
goto v___jp_3500_;
}
v___jp_3538_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
lean_inc(v_a_3537_);
v___x_3539_ = lean_array_push(v_fst_3512_, v_a_3537_);
v___x_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
lean_ctor_set(v___x_3540_, 1, v_snd_3513_);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_fst_3508_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v_a_3501_ = v___x_3541_;
goto v___jp_3500_;
}
v___jp_3542_:
{
if (v___y_3545_ == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref(v___y_3544_);
v___x_3546_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_3543_, v___y_3545_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3547_; 
lean_dec_ref_known(v___x_3546_, 1);
lean_inc(v_a_3537_);
v___x_3547_ = lean_array_push(v_fst_3512_, v_a_3537_);
v_fst_3527_ = v_fst_3508_;
v_snd_3528_ = v___x_3547_;
goto v___jp_3526_;
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v_a_3548_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3546_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3546_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v___x_3556_; 
lean_dec_ref(v___y_3543_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_dec(v_fst_3508_);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___y_3544_);
return v___x_3556_;
}
}
v___jp_3557_:
{
if (v___y_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_dec_ref(v___y_3558_);
v___x_3561_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v___y_3559_, v___y_3560_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3562_; 
lean_dec_ref_known(v___x_3561_, 1);
lean_inc(v_a_3537_);
v___x_3562_ = lean_array_push(v_fst_3512_, v_a_3537_);
v_fst_3518_ = v_fst_3508_;
v_snd_3519_ = v___x_3562_;
goto v___jp_3517_;
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
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
lean_object* v___x_3571_; 
lean_dec_ref(v___y_3559_);
lean_del_object(v___x_3515_);
lean_dec(v_snd_3513_);
lean_dec(v_fst_3512_);
lean_del_object(v___x_3510_);
lean_dec(v_fst_3508_);
v___x_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___y_3558_);
return v___x_3571_;
}
}
}
}
}
v___jp_3500_:
{
size_t v___x_3502_; size_t v___x_3503_; 
v___x_3502_ = ((size_t)1ULL);
v___x_3503_ = lean_usize_add(v_i_3489_, v___x_3502_);
v_i_3489_ = v___x_3503_;
v_b_3490_ = v_a_3501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4___boxed(lean_object* v_as_3829_, lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_b_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
size_t v_sz_boxed_3842_; size_t v_i_boxed_3843_; lean_object* v_res_3844_; 
v_sz_boxed_3842_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3843_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v_as_3829_, v_sz_boxed_3842_, v_i_boxed_3843_, v_b_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v_as_3829_);
return v_res_3844_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__14));
v___x_3885_ = l_String_toRawSubstring_x27(v___x_3884_);
return v___x_3885_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__20));
v___x_3897_ = l_String_toRawSubstring_x27(v___x_3896_);
return v___x_3897_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23(void){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Array_mkArray0(lean_box(0));
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext(lean_object* v_optConfig_3905_, lean_object* v_lemmas_3906_, uint8_t v_ignoreStarArg_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_){
_start:
{
uint8_t v_starArg_3917_; uint8_t v_starArg_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v_starArg_3917_ = 1;
v_starArg_3918_ = 0;
v___x_3919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__0));
v___x_3920_ = l_Lean_Elab_Tactic_Do_elabConfig___redArg(v_optConfig_3905_, v___x_3919_, v_starArg_3917_, v_a_3908_, v_a_3914_, v_a_3915_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3922_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___x_3920_, 1);
v___x_3922_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_3915_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; size_t v_sz_3929_; size_t v___x_3930_; lean_object* v___x_3931_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v___x_3922_, 1);
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = l_Lean_Syntax_getArg(v_lemmas_3906_, v___x_3924_);
v___x_3926_ = l_Lean_Syntax_getSepArgs(v___x_3925_);
lean_dec(v___x_3925_);
v___x_3927_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__2));
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v_a_3923_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v_sz_3929_ = lean_array_size(v___x_3926_);
v___x_3930_ = ((size_t)0ULL);
v___x_3931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__4(v___x_3926_, v_sz_3929_, v___x_3930_, v___x_3928_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
lean_dec_ref(v___x_3926_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v_snd_3933_; lean_object* v_fst_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_4041_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v_snd_3933_ = lean_ctor_get(v_a_3932_, 1);
v_fst_3934_ = lean_ctor_get(v_a_3932_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_a_3932_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_3936_ = v_a_3932_;
v_isShared_3937_ = v_isSharedCheck_4041_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_snd_3933_);
lean_inc(v_fst_3934_);
lean_dec(v_a_3932_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_4041_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v_fst_3938_; lean_object* v_snd_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_4040_; 
v_fst_3938_ = lean_ctor_get(v_snd_3933_, 0);
v_snd_3939_ = lean_ctor_get(v_snd_3933_, 1);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_snd_3933_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_3941_ = v_snd_3933_;
v_isShared_3942_ = v_isSharedCheck_4040_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_snd_3939_);
lean_inc(v_fst_3938_);
lean_dec(v_snd_3933_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_4040_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v_ref_3943_; lean_object* v_quotContext_3944_; lean_object* v_currMacroScope_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3950_; 
v_ref_3943_ = lean_ctor_get(v_a_3914_, 5);
v_quotContext_3944_ = lean_ctor_get(v_a_3914_, 10);
v_currMacroScope_3945_ = lean_ctor_get(v_a_3914_, 11);
v___x_3946_ = l_Lean_SourceInfo_fromRef(v_ref_3943_, v_starArg_3918_);
v___x_3947_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__3));
v___x_3948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__4));
lean_inc(v___x_3946_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set_tag(v___x_3941_, 2);
lean_ctor_set(v___x_3941_, 1, v___x_3947_);
lean_ctor_set(v___x_3941_, 0, v___x_3946_);
v___x_3950_ = v___x_3941_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v___x_3947_);
v___x_3950_ = v_reuseFailAlloc_4039_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3957_; 
v___x_3951_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__6));
v___x_3952_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__8));
v___x_3953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__10));
v___x_3954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__12));
v___x_3955_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__13));
lean_inc(v___x_3946_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set_tag(v___x_3936_, 2);
lean_ctor_set(v___x_3936_, 1, v___x_3955_);
lean_ctor_set(v___x_3936_, 0, v___x_3946_);
v___x_3957_ = v___x_3936_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_4038_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3958_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__15);
v___x_3959_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__16));
lean_inc_n(v_currMacroScope_3945_, 2);
lean_inc_n(v_quotContext_3944_, 2);
v___x_3960_ = l_Lean_addMacroScope(v_quotContext_3944_, v___x_3959_, v_currMacroScope_3945_);
v___x_3961_ = lean_box(0);
lean_inc_n(v___x_3946_, 14);
v___x_3962_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3946_);
lean_ctor_set(v___x_3962_, 1, v___x_3958_);
lean_ctor_set(v___x_3962_, 2, v___x_3960_);
lean_ctor_set(v___x_3962_, 3, v___x_3961_);
v___x_3963_ = l_Lean_Syntax_node2(v___x_3946_, v___x_3954_, v___x_3957_, v___x_3962_);
v___x_3964_ = l_Lean_Syntax_node1(v___x_3946_, v___x_3953_, v___x_3963_);
v___x_3965_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__18));
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__19));
v___x_3967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3946_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__21);
v___x_3969_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__22));
v___x_3970_ = l_Lean_addMacroScope(v_quotContext_3944_, v___x_3969_, v_currMacroScope_3945_);
v___x_3971_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3946_);
lean_ctor_set(v___x_3971_, 1, v___x_3968_);
lean_ctor_set(v___x_3971_, 2, v___x_3970_);
lean_ctor_set(v___x_3971_, 3, v___x_3961_);
v___x_3972_ = l_Lean_Syntax_node2(v___x_3946_, v___x_3965_, v___x_3967_, v___x_3971_);
v___x_3973_ = l_Lean_Syntax_node1(v___x_3946_, v___x_3953_, v___x_3972_);
v___x_3974_ = l_Lean_Syntax_node2(v___x_3946_, v___x_3952_, v___x_3964_, v___x_3973_);
v___x_3975_ = l_Lean_Syntax_node1(v___x_3946_, v___x_3951_, v___x_3974_);
v___x_3976_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23, &l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23_once, _init_l_Lean_Elab_Tactic_Do_mkSpecContext___closed__23);
v___x_3977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3946_);
lean_ctor_set(v___x_3977_, 1, v___x_3952_);
lean_ctor_set(v___x_3977_, 2, v___x_3976_);
v___x_3978_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__24));
v___x_3979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3946_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__25));
v___x_3981_ = l_Lean_Syntax_SepArray_ofElems(v___x_3980_, v_fst_3938_);
lean_dec(v_fst_3938_);
v___x_3982_ = l_Array_append___redArg(v___x_3976_, v___x_3981_);
lean_dec_ref(v___x_3981_);
v___x_3983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3946_);
lean_ctor_set(v___x_3983_, 1, v___x_3952_);
lean_ctor_set(v___x_3983_, 2, v___x_3982_);
v___x_3984_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__26));
v___x_3985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3946_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = l_Lean_Syntax_node3(v___x_3946_, v___x_3952_, v___x_3979_, v___x_3983_, v___x_3985_);
lean_inc_ref_n(v___x_3977_, 2);
v___x_3987_ = l_Lean_Syntax_node6(v___x_3946_, v___x_3948_, v___x_3950_, v___x_3975_, v___x_3977_, v___x_3977_, v___x_3986_, v___x_3977_);
v___x_3988_ = 0;
v___x_3989_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_mkSpecContext___closed__27));
v___x_3990_ = l_Lean_Elab_Tactic_mkSimpContext(v___x_3987_, v_starArg_3918_, v___x_3988_, v_ignoreStarArg_3907_, v___x_3989_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
lean_dec(v___x_3987_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4029_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4029_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4029_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v_specThms_3996_; lean_object* v___y_3997_; uint8_t v___x_4007_; 
v___x_4007_ = lean_unbox(v_snd_3939_);
lean_dec(v_snd_3939_);
if (v___x_4007_ == 0)
{
v_specThms_3996_ = v_fst_3934_;
v___y_3997_ = v_a_3912_;
goto v___jp_3995_;
}
else
{
if (v_ignoreStarArg_3907_ == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_Meta_getPropHyps(v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; size_t v_sz_4010_; lean_object* v___x_4011_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v_sz_4010_ = lean_array_size(v_a_4009_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_a_4009_, v_sz_4010_, v___x_3930_, v_fst_3934_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
lean_dec(v_a_4009_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v_specThms_3996_ = v_a_4012_;
v___y_3997_ = v_a_3912_;
goto v___jp_3995_;
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_del_object(v___x_3993_);
lean_dec(v_a_3991_);
lean_dec(v_a_3921_);
v_a_4013_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4011_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4011_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_del_object(v___x_3993_);
lean_dec(v_a_3991_);
lean_dec(v_fst_3934_);
lean_dec(v_a_3921_);
v_a_4021_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4008_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4008_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
v_specThms_3996_ = v_fst_3934_;
v___y_3997_ = v_a_3912_;
goto v___jp_3995_;
}
}
v___jp_3995_:
{
lean_object* v_lctx_3998_; lean_object* v_ctx_3999_; lean_object* v_simprocs_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
v_lctx_3998_ = lean_ctor_get(v___y_3997_, 2);
v_ctx_3999_ = lean_ctor_get(v_a_3991_, 0);
lean_inc_ref(v_ctx_3999_);
v_simprocs_4000_ = lean_ctor_get(v_a_3991_, 1);
lean_inc_ref(v_simprocs_4000_);
lean_dec(v_a_3991_);
v___x_4001_ = lean_box(1);
lean_inc_ref(v_lctx_3998_);
v___x_4002_ = lean_local_ctx_num_indices(v_lctx_3998_);
v___x_4003_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4003_, 0, v_a_3921_);
lean_ctor_set(v___x_4003_, 1, v_specThms_3996_);
lean_ctor_set(v___x_4003_, 2, v_ctx_3999_);
lean_ctor_set(v___x_4003_, 3, v_simprocs_4000_);
lean_ctor_set(v___x_4003_, 4, v___x_4001_);
lean_ctor_set(v___x_4003_, 5, v___x_4002_);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_4003_);
v___x_4005_ = v___x_3993_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec(v_snd_3939_);
lean_dec(v_fst_3934_);
lean_dec(v_a_3921_);
v_a_4030_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_3990_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_3990_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
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
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec(v_a_3921_);
v_a_4042_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_3931_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_3931_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
lean_dec(v_a_3921_);
v_a_4050_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_3922_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_3922_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
v_a_4058_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_3920_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_3920_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_mkSpecContext___boxed(lean_object* v_optConfig_4066_, lean_object* v_lemmas_4067_, lean_object* v_ignoreStarArg_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_){
_start:
{
uint8_t v_ignoreStarArg_boxed_4078_; lean_object* v_res_4079_; 
v_ignoreStarArg_boxed_4078_ = lean_unbox(v_ignoreStarArg_4068_);
v_res_4079_ = l_Lean_Elab_Tactic_Do_mkSpecContext(v_optConfig_4066_, v_lemmas_4067_, v_ignoreStarArg_boxed_4078_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec_ref(v_a_4073_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_lemmas_4067_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(lean_object* v_00_u03b1_4080_, lean_object* v_msg_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___redArg(v_msg_4081_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1___boxed(lean_object* v_00_u03b1_4092_, lean_object* v_msg_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__1(v_00_u03b1_4092_, v_msg_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(lean_object* v_00_u03b1_4104_, lean_object* v_constName_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___redArg(v_constName_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3___boxed(lean_object* v_00_u03b1_4116_, lean_object* v_constName_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3(v_00_u03b1_4116_, v_constName_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(lean_object* v_as_4128_, size_t v_sz_4129_, size_t v_i_4130_, lean_object* v_b_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___redArg(v_as_4128_, v_sz_4129_, v_i_4130_, v_b_4131_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5___boxed(lean_object* v_as_4142_, lean_object* v_sz_4143_, lean_object* v_i_4144_, lean_object* v_b_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
size_t v_sz_boxed_4155_; size_t v_i_boxed_4156_; lean_object* v_res_4157_; 
v_sz_boxed_4155_ = lean_unbox_usize(v_sz_4143_);
lean_dec(v_sz_4143_);
v_i_boxed_4156_ = lean_unbox_usize(v_i_4144_);
lean_dec(v_i_4144_);
v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__5(v_as_4142_, v_sz_boxed_4155_, v_i_boxed_4156_, v_b_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec_ref(v_as_4142_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(lean_object* v_00_u03b1_4158_, lean_object* v_ref_4159_, lean_object* v_constName_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___redArg(v_ref_4159_, v_constName_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3___boxed(lean_object* v_00_u03b1_4171_, lean_object* v_ref_4172_, lean_object* v_constName_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3(v_00_u03b1_4171_, v_ref_4172_, v_constName_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v_ref_4172_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_4184_, lean_object* v_ref_4185_, lean_object* v_msg_4186_, lean_object* v_declHint_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___redArg(v_ref_4185_, v_msg_4186_, v_declHint_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4198_, lean_object* v_ref_4199_, lean_object* v_msg_4200_, lean_object* v_declHint_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4(v_00_u03b1_4198_, v_ref_4199_, v_msg_4200_, v_declHint_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v_ref_4199_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_msg_4212_, lean_object* v_declHint_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_msg_4212_, v_declHint_4213_, v___y_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_msg_4224_, lean_object* v_declHint_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__7_spec__8(v_msg_4224_, v_declHint_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(lean_object* v_00_u03b1_4236_, lean_object* v_ref_4237_, lean_object* v_msg_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___redArg(v_ref_4237_, v_msg_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b1_4249_, lean_object* v_ref_4250_, lean_object* v_msg_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_mkSpecContext_spec__3_spec__3_spec__4_spec__8(v_00_u03b1_4249_, v_ref_4250_, v_msg_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v_ref_4250_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_4262_, v___x_4263_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed(lean_object* v___x_4273_, lean_object* v___x_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0(v___x_4273_, v___x_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v_inheritedTraceOptions_4292_; lean_object* v___x_4293_; 
v_inheritedTraceOptions_4292_ = lean_ctor_get(v___y_4289_, 13);
lean_inc_ref(v_inheritedTraceOptions_4292_);
v___x_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4293_, 0, v_inheritedTraceOptions_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1___boxed(lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__1(v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_options_4311_; lean_object* v___x_4312_; 
v_options_4311_ = lean_ctor_get(v___y_4308_, 2);
lean_inc_ref(v_options_4311_);
v___x_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4312_, 0, v_options_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2___boxed(lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__2(v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
return v_res_4321_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4324_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_4325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_4327_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4326_, v___x_4325_, v___x_4324_);
return v___x_4327_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5(void){
_start:
{
lean_object* v___x_4330_; lean_object* v___f_4331_; lean_object* v___f_4332_; lean_object* v___x_4333_; 
v___x_4330_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__4);
v___f_4331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_4333_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4332_, v___f_4331_, v___x_4330_);
return v___x_4333_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4334_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__5);
v___x_4335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__2));
v___x_4337_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_4336_, v___x_4335_, v___x_4334_);
return v___x_4337_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7(void){
_start:
{
lean_object* v___x_4338_; lean_object* v___f_4339_; lean_object* v___f_4340_; lean_object* v___x_4341_; 
v___x_4338_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__6);
v___f_4339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__0));
v___x_4341_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_4340_, v___f_4339_, v___x_4338_);
return v___x_4341_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8(void){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_instMonadEIO(lean_box(0));
return v___x_4342_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__8);
v___x_4344_ = l_StateRefT_x27_instMonad___redArg(v___x_4343_);
return v___x_4344_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = l_Lean_Core_instMonadTraceCoreM;
v___x_4350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4351_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_4350_, v___x_4349_);
return v___x_4351_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___f_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__14);
v___f_4353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4354_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4353_, v___x_4352_);
return v___x_4354_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4355_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__15);
v___x_4356_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4357_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_4356_, v___x_4355_);
return v___x_4357_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___f_4359_; lean_object* v___x_4360_; 
v___x_4358_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__16);
v___f_4359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4360_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4359_, v___x_4358_);
return v___x_4360_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___f_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__17);
v___f_4362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___x_4363_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4362_, v___x_4361_);
return v___x_4363_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___f_4365_; lean_object* v___x_4366_; 
v___x_4364_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__18);
v___f_4365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___x_4366_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_4365_, v___x_4364_);
return v___x_4366_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_4373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__23));
v___x_4374_ = l_Lean_Name_append(v___x_4373_, v___x_4372_);
return v___x_4374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___f_4377_; 
v___x_4375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__3));
v___x_4376_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_4377_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4377_, 0, v___x_4376_);
lean_closure_set(v___f_4377_, 1, v___x_4375_);
return v___f_4377_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26(void){
_start:
{
lean_object* v___f_4378_; lean_object* v___f_4379_; lean_object* v___f_4380_; 
v___f_4378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4379_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__25);
v___f_4380_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4380_, 0, v___f_4379_);
lean_closure_set(v___f_4380_, 1, v___f_4378_);
return v___f_4380_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27(void){
_start:
{
lean_object* v___f_4381_; lean_object* v___f_4382_; lean_object* v___f_4383_; 
v___f_4381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__1));
v___f_4382_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__26);
v___f_4383_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4383_, 0, v___f_4382_);
lean_closure_set(v___f_4383_, 1, v___f_4381_);
return v___f_4383_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28(void){
_start:
{
lean_object* v___f_4384_; lean_object* v___f_4385_; lean_object* v___f_4386_; 
v___f_4384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instMonadLiftSimpMVCGenM___closed__0));
v___f_4385_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__27);
v___f_4386_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4386_, 0, v___f_4385_);
lean_closure_set(v___f_4386_, 1, v___f_4384_);
return v___f_4386_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30(void){
_start:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__29));
v___x_4389_ = l_Lean_stringToMessageData(v___x_4388_);
return v___x_4389_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32(void){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__31));
v___x_4392_ = l_Lean_stringToMessageData(v___x_4391_);
return v___x_4392_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34(void){
_start:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__33));
v___x_4395_ = l_Lean_stringToMessageData(v___x_4394_);
return v___x_4395_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36(void){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__35));
v___x_4398_ = l_Lean_stringToMessageData(v___x_4397_);
return v___x_4398_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38(void){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__37));
v___x_4401_ = l_Lean_stringToMessageData(v___x_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(lean_object* v_xs_4402_, lean_object* v_k_4403_, lean_object* v_runInBase_4404_, lean_object* v_i_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v___y_4414_; lean_object* v___y_4415_; uint8_t v___y_4416_; lean_object* v___y_4421_; lean_object* v_a_4422_; lean_object* v_a_4426_; lean_object* v___y_4429_; lean_object* v___x_4431_; lean_object* v_toMonadRef_4432_; lean_object* v___x_4433_; lean_object* v_toApplicative_4434_; lean_object* v_toFunctor_4435_; lean_object* v_toSeq_4436_; lean_object* v_toSeqLeft_4437_; lean_object* v_toSeqRight_4438_; lean_object* v___f_4439_; lean_object* v___f_4440_; lean_object* v___f_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___f_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v_toApplicative_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4548_; 
v___x_4431_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__7);
v_toMonadRef_4432_ = lean_ctor_get(v___x_4431_, 0);
v___x_4433_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__9);
v_toApplicative_4434_ = lean_ctor_get(v___x_4433_, 0);
v_toFunctor_4435_ = lean_ctor_get(v_toApplicative_4434_, 0);
v_toSeq_4436_ = lean_ctor_get(v_toApplicative_4434_, 2);
v_toSeqLeft_4437_ = lean_ctor_get(v_toApplicative_4434_, 3);
v_toSeqRight_4438_ = lean_ctor_get(v_toApplicative_4434_, 4);
v___f_4439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__10));
v___f_4440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__11));
lean_inc_ref_n(v_toFunctor_4435_, 2);
v___f_4441_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4441_, 0, v_toFunctor_4435_);
v___f_4442_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4442_, 0, v_toFunctor_4435_);
v___x_4443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___f_4441_);
lean_ctor_set(v___x_4443_, 1, v___f_4442_);
lean_inc(v_toSeqRight_4438_);
v___f_4444_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4444_, 0, v_toSeqRight_4438_);
lean_inc(v_toSeqLeft_4437_);
v___f_4445_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4445_, 0, v_toSeqLeft_4437_);
lean_inc(v_toSeq_4436_);
v___f_4446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4446_, 0, v_toSeq_4436_);
v___x_4447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4443_);
lean_ctor_set(v___x_4447_, 1, v___f_4439_);
lean_ctor_set(v___x_4447_, 2, v___f_4446_);
lean_ctor_set(v___x_4447_, 3, v___f_4445_);
lean_ctor_set(v___x_4447_, 4, v___f_4444_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
lean_ctor_set(v___x_4448_, 1, v___f_4440_);
v___x_4449_ = l_StateRefT_x27_instMonad___redArg(v___x_4448_);
v_toApplicative_4450_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4548_ == 0)
{
lean_object* v_unused_4549_; 
v_unused_4549_ = lean_ctor_get(v___x_4449_, 1);
lean_dec(v_unused_4549_);
v___x_4452_ = v___x_4449_;
v_isShared_4453_ = v_isSharedCheck_4548_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_toApplicative_4450_);
lean_dec(v___x_4449_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4548_;
goto v_resetjp_4451_;
}
v___jp_4413_:
{
if (v___y_4416_ == 0)
{
if (lean_obj_tag(v___y_4415_) == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_dec_ref_known(v___y_4415_, 2);
lean_dec_ref(v___y_4414_);
v___x_4417_ = lean_unsigned_to_nat(1u);
v___x_4418_ = lean_nat_add(v_i_4405_, v___x_4417_);
lean_dec(v_i_4405_);
v_i_4405_ = v___x_4418_;
goto _start;
}
else
{
lean_dec_ref_known(v___y_4415_, 2);
lean_dec(v_i_4405_);
lean_dec_ref(v_runInBase_4404_);
lean_dec(v_k_4403_);
return v___y_4414_;
}
}
else
{
lean_dec_ref(v___y_4415_);
lean_dec(v_i_4405_);
lean_dec_ref(v_runInBase_4404_);
lean_dec(v_k_4403_);
return v___y_4414_;
}
}
v___jp_4420_:
{
uint8_t v___x_4423_; 
v___x_4423_ = l_Lean_Exception_isInterrupt(v_a_4422_);
if (v___x_4423_ == 0)
{
uint8_t v___x_4424_; 
lean_inc_ref(v_a_4422_);
v___x_4424_ = l_Lean_Exception_isRuntime(v_a_4422_);
v___y_4414_ = v___y_4421_;
v___y_4415_ = v_a_4422_;
v___y_4416_ = v___x_4424_;
goto v___jp_4413_;
}
else
{
v___y_4414_ = v___y_4421_;
v___y_4415_ = v_a_4422_;
v___y_4416_ = v___x_4423_;
goto v___jp_4413_;
}
}
v___jp_4425_:
{
lean_object* v___x_4427_; 
lean_inc_ref(v_a_4426_);
v___x_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4427_, 0, v_a_4426_);
v___y_4421_ = v___x_4427_;
v_a_4422_ = v_a_4426_;
goto v___jp_4420_;
}
v___jp_4428_:
{
if (lean_obj_tag(v___y_4429_) == 0)
{
lean_dec(v_i_4405_);
lean_dec_ref(v_runInBase_4404_);
lean_dec(v_k_4403_);
return v___y_4429_;
}
else
{
lean_object* v_a_4430_; 
v_a_4430_ = lean_ctor_get(v___y_4429_, 0);
lean_inc(v_a_4430_);
v___y_4421_ = v___y_4429_;
v_a_4422_ = v_a_4430_;
goto v___jp_4420_;
}
}
v_resetjp_4451_:
{
lean_object* v_toFunctor_4454_; lean_object* v_toSeq_4455_; lean_object* v_toSeqLeft_4456_; lean_object* v_toSeqRight_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4546_; 
v_toFunctor_4454_ = lean_ctor_get(v_toApplicative_4450_, 0);
v_toSeq_4455_ = lean_ctor_get(v_toApplicative_4450_, 2);
v_toSeqLeft_4456_ = lean_ctor_get(v_toApplicative_4450_, 3);
v_toSeqRight_4457_ = lean_ctor_get(v_toApplicative_4450_, 4);
v_isSharedCheck_4546_ = !lean_is_exclusive(v_toApplicative_4450_);
if (v_isSharedCheck_4546_ == 0)
{
lean_object* v_unused_4547_; 
v_unused_4547_ = lean_ctor_get(v_toApplicative_4450_, 1);
lean_dec(v_unused_4547_);
v___x_4459_ = v_toApplicative_4450_;
v_isShared_4460_ = v_isSharedCheck_4546_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_toSeqRight_4457_);
lean_inc(v_toSeqLeft_4456_);
lean_inc(v_toSeq_4455_);
lean_inc(v_toFunctor_4454_);
lean_dec(v_toApplicative_4450_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4546_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___f_4461_; lean_object* v___f_4462_; lean_object* v___f_4463_; lean_object* v___f_4464_; lean_object* v___x_4465_; lean_object* v___f_4466_; lean_object* v___f_4467_; lean_object* v___f_4468_; lean_object* v___x_4470_; 
v___f_4461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__12));
v___f_4462_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__13));
lean_inc_ref(v_toFunctor_4454_);
v___f_4463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4463_, 0, v_toFunctor_4454_);
v___f_4464_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4464_, 0, v_toFunctor_4454_);
v___x_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___f_4463_);
lean_ctor_set(v___x_4465_, 1, v___f_4464_);
v___f_4466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4466_, 0, v_toSeqRight_4457_);
v___f_4467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4467_, 0, v_toSeqLeft_4456_);
v___f_4468_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4468_, 0, v_toSeq_4455_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 4, v___f_4466_);
lean_ctor_set(v___x_4459_, 3, v___f_4467_);
lean_ctor_set(v___x_4459_, 2, v___f_4468_);
lean_ctor_set(v___x_4459_, 1, v___f_4461_);
lean_ctor_set(v___x_4459_, 0, v___x_4465_);
v___x_4470_ = v___x_4459_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4545_, 1, v___f_4461_);
lean_ctor_set(v_reuseFailAlloc_4545_, 2, v___f_4468_);
lean_ctor_set(v_reuseFailAlloc_4545_, 3, v___f_4467_);
lean_ctor_set(v_reuseFailAlloc_4545_, 4, v___f_4466_);
v___x_4470_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4472_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set(v___x_4452_, 1, v___f_4462_);
lean_ctor_set(v___x_4452_, 0, v___x_4470_);
v___x_4472_ = v___x_4452_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v___f_4462_);
v___x_4472_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; uint8_t v___x_4477_; 
v___x_4473_ = l_StateRefT_x27_instMonad___redArg(v___x_4472_);
v___x_4474_ = l_ReaderT_instMonad___redArg(v___x_4473_);
v___x_4475_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__19);
v___x_4476_ = lean_array_get_size(v_xs_4402_);
v___x_4477_ = lean_nat_dec_lt(v_i_4405_, v___x_4476_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4478_; 
lean_dec_ref(v___x_4474_);
lean_dec(v_i_4405_);
lean_inc(v_a_4411_);
lean_inc_ref(v_a_4410_);
lean_inc(v_a_4409_);
lean_inc_ref(v_a_4408_);
lean_inc(v_a_4407_);
lean_inc_ref(v_a_4406_);
v___x_4478_ = lean_apply_9(v_runInBase_4404_, lean_box(0), v_k_4403_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, lean_box(0));
return v___x_4478_;
}
else
{
lean_object* v_x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___f_4482_; lean_object* v___x_4483_; 
v_x_4479_ = lean_array_fget_borrowed(v_xs_4402_, v_i_4405_);
v___x_4480_ = l_Lean_Expr_fvarId_x21(v_x_4479_);
v___x_4481_ = lean_unsigned_to_nat(100u);
v___f_4482_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4482_, 0, v___x_4480_);
lean_closure_set(v___f_4482_, 1, v___x_4481_);
v___x_4483_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4482_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___f_4485_; lean_object* v___x_4486_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___f_4485_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__20));
v___x_4486_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4485_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___f_4488_; lean_object* v___x_4489_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___f_4488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__21));
v___x_4489_ = l_Lean_Elab_Tactic_Do_liftSimpM___redArg(v___f_4488_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; uint8_t v_hasTrace_4491_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v_hasTrace_4491_ = lean_ctor_get_uint8(v_a_4490_, sizeof(void*)*1);
if (v_hasTrace_4491_ == 0)
{
lean_dec(v_a_4490_);
lean_dec(v_a_4487_);
lean_dec_ref(v___x_4474_);
goto v___jp_4492_;
}
else
{
lean_object* v___x_4495_; lean_object* v___x_4496_; uint8_t v___x_4497_; 
v___x_4495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_540456248____hygCtx___hyg_2_));
v___x_4496_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__24);
v___x_4497_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_a_4487_, v_a_4490_, v___x_4496_);
lean_dec(v_a_4490_);
lean_dec(v_a_4487_);
if (v___x_4497_ == 0)
{
lean_dec_ref(v___x_4474_);
goto v___jp_4492_;
}
else
{
lean_object* v_proof_4498_; lean_object* v___f_4499_; lean_object* v___x_4500_; lean_object* v___y_4502_; 
v_proof_4498_ = lean_ctor_get(v_a_4484_, 2);
v___f_4499_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__28);
v___x_4500_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__30);
switch(lean_obj_tag(v_proof_4498_))
{
case 0:
{
lean_object* v_declName_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v_declName_4516_ = lean_ctor_get(v_proof_4498_, 0);
v___x_4517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__32);
lean_inc(v_declName_4516_);
v___x_4518_ = l_Lean_MessageData_ofName(v_declName_4516_);
v___x_4519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4517_);
lean_ctor_set(v___x_4519_, 1, v___x_4518_);
v___y_4502_ = v___x_4519_;
goto v___jp_4501_;
}
case 1:
{
lean_object* v_fvarId_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v_fvarId_4520_ = lean_ctor_get(v_proof_4498_, 0);
v___x_4521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__34);
lean_inc(v_fvarId_4520_);
v___x_4522_ = l_Lean_mkFVar(v_fvarId_4520_);
v___x_4523_ = l_Lean_MessageData_ofExpr(v___x_4522_);
v___x_4524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4521_);
lean_ctor_set(v___x_4524_, 1, v___x_4523_);
v___y_4502_ = v___x_4524_;
goto v___jp_4501_;
}
default: 
{
lean_object* v_ref_4525_; lean_object* v_proof_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v_ref_4525_ = lean_ctor_get(v_proof_4498_, 1);
v_proof_4526_ = lean_ctor_get(v_proof_4498_, 2);
v___x_4527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__36);
lean_inc(v_ref_4525_);
v___x_4528_ = l_Lean_MessageData_ofSyntax(v_ref_4525_);
v___x_4529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4527_);
lean_ctor_set(v___x_4529_, 1, v___x_4528_);
v___x_4530_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38, &l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38_once, _init_l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___closed__38);
v___x_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4529_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
lean_inc_ref(v_proof_4526_);
v___x_4532_ = l_Lean_MessageData_ofExpr(v_proof_4526_);
v___x_4533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4531_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___y_4502_ = v___x_4533_;
goto v___jp_4501_;
}
}
v___jp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_5420__overap_4504_; lean_object* v___x_4505_; 
v___x_4503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4500_);
lean_ctor_set(v___x_4503_, 1, v___y_4502_);
lean_inc_ref(v_toMonadRef_4432_);
v___x_5420__overap_4504_ = l_Lean_addTrace___redArg(v___x_4474_, v___x_4475_, v_toMonadRef_4432_, v___f_4499_, v___x_4495_, v___x_4503_);
lean_inc(v_a_4411_);
lean_inc_ref(v_a_4410_);
lean_inc(v_a_4409_);
lean_inc_ref(v_a_4408_);
lean_inc(v_a_4407_);
lean_inc_ref(v_a_4406_);
v___x_4505_ = lean_apply_7(v___x_5420__overap_4504_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, lean_box(0));
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4507_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v___x_4505_, 1);
lean_inc_ref(v_runInBase_4404_);
lean_inc(v_k_4403_);
v___x_4507_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4405_, v_a_4484_, v_xs_4402_, v_k_4403_, v_runInBase_4404_, v_a_4506_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
v___y_4429_ = v___x_4507_;
goto v___jp_4428_;
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec(v_a_4484_);
v_a_4508_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4505_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4505_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
lean_inc(v_a_4508_);
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
v___y_4421_ = v___x_4513_;
v_a_4422_ = v_a_4508_;
goto v___jp_4420_;
}
}
}
}
}
}
v___jp_4492_:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_box(0);
lean_inc_ref(v_runInBase_4404_);
lean_inc(v_k_4403_);
v___x_4494_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4405_, v_a_4484_, v_xs_4402_, v_k_4403_, v_runInBase_4404_, v___x_4493_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
v___y_4429_ = v___x_4494_;
goto v___jp_4428_;
}
}
else
{
lean_object* v_a_4534_; 
lean_dec(v_a_4487_);
lean_dec(v_a_4484_);
lean_dec_ref(v___x_4474_);
v_a_4534_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v___x_4489_, 1);
v_a_4426_ = v_a_4534_;
goto v___jp_4425_;
}
}
else
{
lean_object* v_a_4535_; 
lean_dec(v_a_4484_);
lean_dec_ref(v___x_4474_);
v_a_4535_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4486_, 1);
v_a_4426_ = v_a_4535_;
goto v___jp_4425_;
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec_ref(v___x_4474_);
v_a_4536_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4483_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4483_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
lean_inc(v_a_4536_);
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
v___y_4421_ = v___x_4541_;
v_a_4422_ = v_a_4536_;
goto v___jp_4420_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(lean_object* v_i_4550_, lean_object* v_a_4551_, lean_object* v_xs_4552_, lean_object* v_k_4553_, lean_object* v_runInBase_4554_, lean_object* v_____r_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_config_4563_; lean_object* v_specThms_4564_; lean_object* v_simpCtx_4565_; lean_object* v_simprocs_4566_; lean_object* v_jps_4567_; lean_object* v_initialCtxSize_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v_config_4563_ = lean_ctor_get(v___y_4556_, 0);
v_specThms_4564_ = lean_ctor_get(v___y_4556_, 1);
v_simpCtx_4565_ = lean_ctor_get(v___y_4556_, 2);
v_simprocs_4566_ = lean_ctor_get(v___y_4556_, 3);
v_jps_4567_ = lean_ctor_get(v___y_4556_, 4);
v_initialCtxSize_4568_ = lean_ctor_get(v___y_4556_, 5);
v___x_4569_ = lean_unsigned_to_nat(1u);
v___x_4570_ = lean_nat_add(v_i_4550_, v___x_4569_);
lean_inc_ref(v_specThms_4564_);
v___x_4571_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_specThms_4564_, v_a_4551_);
lean_inc(v_initialCtxSize_4568_);
lean_inc(v_jps_4567_);
lean_inc_ref(v_simprocs_4566_);
lean_inc_ref(v_simpCtx_4565_);
lean_inc_ref(v_config_4563_);
v___x_4572_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4572_, 0, v_config_4563_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
lean_ctor_set(v___x_4572_, 2, v_simpCtx_4565_);
lean_ctor_set(v___x_4572_, 3, v_simprocs_4566_);
lean_ctor_set(v___x_4572_, 4, v_jps_4567_);
lean_ctor_set(v___x_4572_, 5, v_initialCtxSize_4568_);
v___x_4573_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4552_, v_k_4553_, v_runInBase_4554_, v___x_4570_, v___x_4572_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec_ref_known(v___x_4572_, 6);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3___boxed(lean_object* v_i_4574_, lean_object* v_a_4575_, lean_object* v_xs_4576_, lean_object* v_k_4577_, lean_object* v_runInBase_4578_, lean_object* v_____r_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___lam__3(v_i_4574_, v_a_4575_, v_xs_4576_, v_k_4577_, v_runInBase_4578_, v_____r_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec_ref(v_xs_4576_);
lean_dec(v_i_4574_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg___boxed(lean_object* v_xs_4588_, lean_object* v_k_4589_, lean_object* v_runInBase_4590_, lean_object* v_i_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4588_, v_k_4589_, v_runInBase_4590_, v_i_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec_ref(v_xs_4588_);
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(lean_object* v_m_4600_, lean_object* v_00_u03b1_4601_, lean_object* v_inst_4602_, lean_object* v_xs_4603_, lean_object* v_k_4604_, lean_object* v_runInBase_4605_, lean_object* v_i_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4603_, v_k_4604_, v_runInBase_4605_, v_i_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_);
return v___x_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___boxed(lean_object* v_m_4615_, lean_object* v_00_u03b1_4616_, lean_object* v_inst_4617_, lean_object* v_xs_4618_, lean_object* v_k_4619_, lean_object* v_runInBase_4620_, lean_object* v_i_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop(v_m_4615_, v_00_u03b1_4616_, v_inst_4617_, v_xs_4618_, v_k_4619_, v_runInBase_4620_, v_i_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec_ref(v_xs_4618_);
lean_dec_ref(v_inst_4617_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter___redArg(lean_object* v_ex_4630_, lean_object* v_h__1_4631_, lean_object* v_h__2_4632_){
_start:
{
if (lean_obj_tag(v_ex_4630_) == 0)
{
lean_object* v_ref_4633_; lean_object* v_msg_4634_; lean_object* v___x_4635_; 
lean_dec(v_h__1_4631_);
v_ref_4633_ = lean_ctor_get(v_ex_4630_, 0);
lean_inc(v_ref_4633_);
v_msg_4634_ = lean_ctor_get(v_ex_4630_, 1);
lean_inc_ref(v_msg_4634_);
lean_dec_ref_known(v_ex_4630_, 2);
v___x_4635_ = lean_apply_2(v_h__2_4632_, v_ref_4633_, v_msg_4634_);
return v___x_4635_;
}
else
{
lean_object* v_id_4636_; lean_object* v_extra_4637_; lean_object* v___x_4638_; 
lean_dec(v_h__2_4632_);
v_id_4636_ = lean_ctor_get(v_ex_4630_, 0);
lean_inc(v_id_4636_);
v_extra_4637_ = lean_ctor_get(v_ex_4630_, 1);
lean_inc(v_extra_4637_);
lean_dec_ref_known(v_ex_4630_, 2);
v___x_4638_ = lean_apply_2(v_h__1_4631_, v_id_4636_, v_extra_4637_);
return v___x_4638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop_match__1_splitter(lean_object* v_motive_4639_, lean_object* v_ex_4640_, lean_object* v_h__1_4641_, lean_object* v_h__2_4642_){
_start:
{
if (lean_obj_tag(v_ex_4640_) == 0)
{
lean_object* v_ref_4643_; lean_object* v_msg_4644_; lean_object* v___x_4645_; 
lean_dec(v_h__1_4641_);
v_ref_4643_ = lean_ctor_get(v_ex_4640_, 0);
lean_inc(v_ref_4643_);
v_msg_4644_ = lean_ctor_get(v_ex_4640_, 1);
lean_inc_ref(v_msg_4644_);
lean_dec_ref_known(v_ex_4640_, 2);
v___x_4645_ = lean_apply_2(v_h__2_4642_, v_ref_4643_, v_msg_4644_);
return v___x_4645_;
}
else
{
lean_object* v_id_4646_; lean_object* v_extra_4647_; lean_object* v___x_4648_; 
lean_dec(v_h__2_4642_);
v_id_4646_ = lean_ctor_get(v_ex_4640_, 0);
lean_inc(v_id_4646_);
v_extra_4647_ = lean_ctor_get(v_ex_4640_, 1);
lean_inc(v_extra_4647_);
lean_dec_ref_known(v_ex_4640_, 2);
v___x_4648_ = lean_apply_2(v_h__1_4641_, v_id_4646_, v_extra_4647_);
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(lean_object* v_xs_4649_, lean_object* v_k_4650_, lean_object* v_runInBase_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = lean_unsigned_to_nat(0u);
v___x_4660_ = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_withLocalSpecs_loop___redArg(v_xs_4649_, v_k_4650_, v_runInBase_4651_, v___x_4659_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed(lean_object* v_xs_4661_, lean_object* v_k_4662_, lean_object* v_runInBase_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0(v_xs_4661_, v_k_4662_, v_runInBase_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec_ref(v_xs_4661_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(lean_object* v_inst_4672_, lean_object* v_inst_4673_, lean_object* v_xs_4674_, lean_object* v_k_4675_){
_start:
{
lean_object* v_toBind_4676_; lean_object* v_liftWith_4677_; lean_object* v_restoreM_4678_; lean_object* v___f_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v_toBind_4676_ = lean_ctor_get(v_inst_4672_, 1);
lean_inc(v_toBind_4676_);
lean_dec_ref(v_inst_4672_);
v_liftWith_4677_ = lean_ctor_get(v_inst_4673_, 0);
lean_inc(v_liftWith_4677_);
v_restoreM_4678_ = lean_ctor_get(v_inst_4673_, 1);
lean_inc(v_restoreM_4678_);
lean_dec_ref(v_inst_4673_);
v___f_4679_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4679_, 0, v_xs_4674_);
lean_closure_set(v___f_4679_, 1, v_k_4675_);
v___x_4680_ = lean_apply_2(v_liftWith_4677_, lean_box(0), v___f_4679_);
v___x_4681_ = lean_apply_1(v_restoreM_4678_, lean_box(0));
v___x_4682_ = lean_apply_4(v_toBind_4676_, lean_box(0), lean_box(0), v___x_4680_, v___x_4681_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_withLocalSpecs(lean_object* v_m_4683_, lean_object* v_00_u03b1_4684_, lean_object* v_inst_4685_, lean_object* v_inst_4686_, lean_object* v_xs_4687_, lean_object* v_k_4688_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = l_Lean_Elab_Tactic_Do_withLocalSpecs___redArg(v_inst_4685_, v_inst_4686_, v_xs_4687_, v_k_4688_);
return v___x_4689_;
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
res = l___private_Lean_Elab_Tactic_Do_VCGen_Basic_0__Lean_Elab_Tactic_Do_initFn_00___x40_Lean_Elab_Tactic_Do_VCGen_Basic_1593450264____hygCtx___hyg_4_();
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
