// Lean compiler output
// Module: Lean.Elab.PreDefinition.Basic
// Imports: Init.ShareCommon Lean.Compiler.MetaAttr Lean.Compiler.NoncomputableAttr Lean.Util.CollectLevelParams Lean.Util.NumObjs Lean.Util.NumApps Lean.Meta.AbstractNestedProofs Lean.Meta.ForEachExpr Lean.Meta.Eqns Lean.Meta.LetToHave Lean.Elab.RecAppSyntax Lean.Elab.DefView Lean.Elab.PreDefinition.TerminationHint
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
static lean_object* l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
static lean_object* l_Lean_Elab_shareCommonPreDefs___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_letToHaveValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractNestedProofs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPreDefinition;
lean_object* l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__10;
lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__15;
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompilePartialRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_checkCodomainsLevel_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___boxed(lean_object**);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamTypesPreDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__7;
lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object*, lean_object*);
uint8_t lean_get_ir_phases(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_fixLevelParams___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_applyAttributesOf_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object*);
static lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PreDefinition_filterAttrs(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___boxed(lean_object**);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__11;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_shareCommonPreDefs___closed__2;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_fixLevelParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamTypesPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__3;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__4;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_addAndCompilePartialRec_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_fixLevelParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3;
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_addAndCompileUnsafe_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_diagnostics_threshold_proofSize;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_fixLevelParams___closed__1;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed__const__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_fixLevelParams_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__4;
lean_object* l_Lean_addNoncomputable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_addAndCompilePartialRec_spec__3(lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l_Lean_hasRecAppSyntax(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__6;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_fixLevelParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_levelMVarToParamTypesPreDecls___lam__0(lean_object*);
uint8_t l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_cleanup_letToHave;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(double, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_letToHaveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_addAndCompileUnsafe_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_addAndCompileUnsafe_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ensureNoRecFn___lam__0___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_fixLevelParams___closed__0;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompilePartialRec_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__7;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__6;
lean_object* l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_76__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8;
lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_shareCommonPreDefs___closed__3;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__0;
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_sanitizeNames;
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__2;
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__3;
uint8_t l_Lean_Elab_Modifiers_isMeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_checkCodomainsLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_applyAttributesOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__5;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamTypesPreDecls___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__7;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__5;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ensureNoRecFn___lam__0___closed__0;
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__16;
static lean_object* l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__2;
lean_object* l_Lean_Expr_numApps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0(double, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__8;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__8;
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_fixLevelParams_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Basic___hyg_7_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__0;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Elab_checkNotAlreadyDeclared___at___Lean_Elab_applyVisibility___at___Lean_Elab_mkDeclName___at___Lean_Elab_expandDeclId___at___Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics_threshold;
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_numObjs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isNoncomputable(lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__12;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__2;
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__6;
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__17;
static lean_object* l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0;
static lean_object* l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2;
static lean_object* l_Lean_Elab_shareCommonPreDefs___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2_spec__2_spec__2___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__5;
static lean_object* l_Lean_Elab_letToHaveValue___closed__0;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__0;
static lean_object* l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg___boxed(lean_object**);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor___boxed(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__6;
static lean_object* l_Lean_Elab_initFn___closed__8____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cleanup", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letToHave", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_2 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Enables transforming `let`s to `have`s after elaborating declarations.", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_2 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__8____x40_Lean_Elab_PreDefinition_Basic___hyg_7_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_2 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_3 = l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_4 = l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Basic___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_3 = l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_4 = l_Lean_Elab_initFn___closed__8____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_5 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Elab_instInhabitedPreDefinition___closed__0;
x_2 = 0;
x_3 = 0;
x_4 = 0;
x_5 = 0;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 3, x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedPreDefinition___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedPreDefinition___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Elab_instInhabitedPreDefinition___closed__5;
x_2 = l_Lean_Elab_instInhabitedPreDefinition___closed__4;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_3);
lean_ctor_set(x_8, 4, x_2);
lean_ctor_set(x_8, 5, x_2);
lean_ctor_set(x_8, 6, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedPreDefinition___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PreDefinition_filterAttrs(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Elab_Modifiers_filterAttrs(x_4, x_2);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_dec(x_1);
x_14 = l_Lean_Elab_Modifiers_filterAttrs(x_9, x_2);
x_15 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_11);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_15, 6, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_8, 4);
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_10, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_11, x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_3, x_2, x_18);
lean_ctor_set(x_8, 5, x_16);
lean_ctor_set(x_8, 4, x_13);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_19, x_2, x_8);
x_2 = x_21;
x_3 = x_22;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get_uint8(x_8, sizeof(void*)*7);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
x_29 = lean_ctor_get(x_8, 4);
x_30 = lean_ctor_get(x_8, 5);
x_31 = lean_ctor_get(x_8, 6);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_8);
x_32 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_29, x_4, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_30, x_4, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_uset(x_3, x_2, x_38);
x_40 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_26);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_33);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set(x_40, 6, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*7, x_25);
x_41 = 1;
x_42 = lean_usize_add(x_2, x_41);
x_43 = lean_array_uset(x_39, x_2, x_40);
x_2 = x_42;
x_3 = x_43;
x_5 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___redArg(x_1, x_2, x_3, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___redArg(x_9, x_10, x_1, x_5, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___redArg(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_instantiateMVarsAtPreDecls_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_instantiateMVarsAtPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_4, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_1);
x_13 = l_Lean_Elab_Term_levelMVarToParam___redArg(x_12, x_1, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
lean_ctor_set(x_10, 4, x_14);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_17, x_3, x_10);
x_3 = x_19;
x_4 = x_20;
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
x_28 = lean_ctor_get(x_10, 5);
x_29 = lean_ctor_get(x_10, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_dec(x_10);
lean_inc_ref(x_1);
x_30 = l_Lean_Elab_Term_levelMVarToParam___redArg(x_27, x_1, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_uset(x_4, x_3, x_33);
x_35 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_28);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*7, x_23);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_38 = lean_array_uset(x_34, x_3, x_35);
x_3 = x_37;
x_4 = x_38;
x_7 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_levelMVarToParamTypesPreDecls___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamTypesPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_levelMVarToParamTypesPreDecls___lam__0___boxed), 1, 0);
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___redArg(x_9, x_10, x_11, x_1, x_3, x_5, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Elab_levelMVarToParamTypesPreDecls_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamTypesPreDecls___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_levelMVarToParamTypesPreDecls___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamTypesPreDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_levelMVarToParamTypesPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 5);
lean_inc_ref(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_CollectLevelParams_main(x_9, x_4);
x_12 = l_Lean_CollectLevelParams_main(x_10, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___redArg(x_1, x_2, x_3, x_4, x_11);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__7;
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__6;
x_3 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__8;
x_12 = lean_array_size(x_1);
x_13 = 0;
x_14 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___redArg(x_1, x_12, x_13, x_11, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_free_object(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_ctor_set_tag(x_19, 3);
x_21 = l_Lean_MessageData_ofFormat(x_19);
x_22 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_4);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec_ref(x_19);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(3, 1, 0);
} else {
 x_34 = x_33;
 lean_ctor_set_tag(x_34, 3);
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_4);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec_ref(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_fixLevelParams_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_fixLevelParams_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_7, 4);
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_ctor_get(x_7, 1);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_5, x_4, x_12);
x_14 = lean_replace_expr(x_1, x_9);
lean_dec_ref(x_9);
x_15 = lean_replace_expr(x_1, x_10);
lean_dec_ref(x_10);
lean_inc(x_2);
lean_ctor_set(x_7, 5, x_15);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 1, x_2);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_18 = lean_array_uset(x_13, x_4, x_7);
x_4 = x_17;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*7);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = lean_ctor_get(x_7, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_7);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_uset(x_5, x_4, x_27);
x_29 = lean_replace_expr(x_1, x_24);
lean_dec_ref(x_24);
x_30 = lean_replace_expr(x_1, x_25);
lean_dec_ref(x_25);
lean_inc(x_2);
x_31 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*7, x_21);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_34 = lean_array_uset(x_28, x_4, x_31);
x_4 = x_33;
x_5 = x_34;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
if (x_7 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at___Lean_Elab_fixLevelParams_spec__0(x_4, x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_const___override(x_4, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
else
{
lean_object* x_16; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_13, x_14);
lean_inc_ref(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_fixLevelParams___lam__0___boxed), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_array_size(x_1);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___Lean_Elab_fixLevelParams_spec__1(x_16, x_13, x_17, x_18, x_1);
lean_dec_ref(x_16);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_box(0);
lean_inc(x_20);
x_23 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_20, x_22);
lean_inc_ref(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_fixLevelParams___lam__0___boxed), 3, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_array_size(x_1);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at___Lean_Elab_fixLevelParams_spec__1(x_24, x_20, x_25, x_26, x_1);
lean_dec_ref(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_stringToMessageData(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_fixLevelParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix level params", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_fixLevelParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_fixLevelParams___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fixLevelParams", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_fixLevelParams___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_fixLevelParams___closed__2;
x_2 = l_Lean_Elab_fixLevelParams___closed__1;
x_3 = l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_fixLevelParams___lam__1___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Elab_fixLevelParams___closed__0;
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_fixLevelParams___lam__2___boxed), 9, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_Elab_fixLevelParams___closed__3;
x_16 = 1;
x_17 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__6___boxed), 13, 6);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, x_15);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_12);
lean_closure_set(x_19, 4, x_18);
lean_closure_set(x_19, 5, x_17);
x_20 = lean_box(0);
x_21 = l_Lean_profileitM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__12___redArg(x_13, x_11, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_fixLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Elab_fixLevelParams_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_fixLevelParams_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Elab_fixLevelParams_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_fixLevelParams___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_fixLevelParams___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_fixLevelParams___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_applyAttributesOf_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_20 = l_Lean_Elab_Term_applyAttributesAt(x_18, x_19, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
{
size_t _tmp_4 = x_23;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_12 = x_21;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_array_size(x_1);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_applyAttributesOf_spec__0(x_2, x_10, x_1, x_11, x_12, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_applyAttributesOf_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_applyAttributesOf_spec__0(x_14, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_Elab_applyAttributesOf(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_letToHaveValue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_cleanup_letToHave;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_letToHaveValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_4, 5);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 7);
x_16 = lean_ctor_get(x_4, 8);
x_17 = lean_ctor_get(x_4, 9);
x_18 = lean_ctor_get(x_4, 10);
x_19 = lean_ctor_get(x_4, 11);
x_20 = lean_ctor_get(x_4, 12);
x_21 = l_Lean_Elab_letToHaveValue___closed__0;
x_22 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*3 + 3);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_27 = lean_box(x_26);
switch (lean_obj_tag(x_27)) {
case 2:
{
lean_object* x_28; 
lean_dec_ref(x_24);
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
case 3:
{
lean_object* x_29; 
lean_dec_ref(x_24);
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
case 4:
{
lean_object* x_30; 
lean_dec_ref(x_24);
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_36);
x_37 = l_Lean_replaceRef(x_31, x_13);
lean_dec(x_13);
lean_ctor_set(x_4, 5, x_37);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_34);
x_38 = l_Lean_Meta_isProp(x_34, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_1, 6);
lean_dec(x_42);
x_43 = lean_ctor_get(x_1, 5);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 4);
lean_dec(x_44);
x_45 = lean_ctor_get(x_1, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_1, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec_ref(x_38);
x_50 = l_Lean_Meta_letToHave(x_35, x_2, x_3, x_4, x_5, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_ctor_set(x_1, 5, x_52);
lean_ctor_set(x_50, 0, x_1);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_50);
lean_ctor_set(x_1, 5, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_1);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_24);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec_ref(x_38);
x_61 = l_Lean_Meta_letToHave(x_35, x_2, x_3, x_4, x_5, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_65, 0, x_31);
lean_ctor_set(x_65, 1, x_32);
lean_ctor_set(x_65, 2, x_24);
lean_ctor_set(x_65, 3, x_33);
lean_ctor_set(x_65, 4, x_34);
lean_ctor_set(x_65, 5, x_62);
lean_ctor_set(x_65, 6, x_36);
lean_ctor_set_uint8(x_65, sizeof(void*)*7, x_26);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_24);
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_4);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_71 = !lean_is_exclusive(x_38);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_38, 0);
lean_dec(x_72);
lean_ctor_set(x_38, 0, x_1);
return x_38;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_38, 1);
lean_inc(x_73);
lean_dec(x_38);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec_ref(x_4);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_24);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_38);
if (x_75 == 0)
{
return x_38;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_38, 0);
x_77 = lean_ctor_get(x_38, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_38);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
lean_object* x_79; 
lean_dec_ref(x_24);
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_6);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_80 = lean_ctor_get(x_4, 0);
x_81 = lean_ctor_get(x_4, 1);
x_82 = lean_ctor_get(x_4, 2);
x_83 = lean_ctor_get(x_4, 3);
x_84 = lean_ctor_get(x_4, 4);
x_85 = lean_ctor_get(x_4, 5);
x_86 = lean_ctor_get(x_4, 6);
x_87 = lean_ctor_get(x_4, 7);
x_88 = lean_ctor_get(x_4, 8);
x_89 = lean_ctor_get(x_4, 9);
x_90 = lean_ctor_get(x_4, 10);
x_91 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_92 = lean_ctor_get(x_4, 11);
x_93 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_94 = lean_ctor_get(x_4, 12);
lean_inc(x_94);
lean_inc(x_92);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_4);
x_95 = l_Lean_Elab_letToHaveValue___closed__0;
x_96 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_82, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_6);
return x_97;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_98);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*3 + 3);
if (x_99 == 0)
{
uint8_t x_100; lean_object* x_101; 
x_100 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_101 = lean_box(x_100);
switch (lean_obj_tag(x_101)) {
case 2:
{
lean_object* x_102; 
lean_dec_ref(x_98);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_6);
return x_102;
}
case 3:
{
lean_object* x_103; 
lean_dec_ref(x_98);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_6);
return x_103;
}
case 4:
{
lean_object* x_104; 
lean_dec_ref(x_98);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_6);
return x_104;
}
default: 
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_101);
x_105 = lean_ctor_get(x_1, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_1, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_110);
x_111 = l_Lean_replaceRef(x_105, x_85);
lean_dec(x_85);
x_112 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_112, 0, x_80);
lean_ctor_set(x_112, 1, x_81);
lean_ctor_set(x_112, 2, x_82);
lean_ctor_set(x_112, 3, x_83);
lean_ctor_set(x_112, 4, x_84);
lean_ctor_set(x_112, 5, x_111);
lean_ctor_set(x_112, 6, x_86);
lean_ctor_set(x_112, 7, x_87);
lean_ctor_set(x_112, 8, x_88);
lean_ctor_set(x_112, 9, x_89);
lean_ctor_set(x_112, 10, x_90);
lean_ctor_set(x_112, 11, x_92);
lean_ctor_set(x_112, 12, x_94);
lean_ctor_set_uint8(x_112, sizeof(void*)*13, x_91);
lean_ctor_set_uint8(x_112, sizeof(void*)*13 + 1, x_93);
lean_inc(x_5);
lean_inc_ref(x_112);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_108);
x_113 = l_Lean_Meta_isProp(x_108, x_2, x_3, x_112, x_5, x_6);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_116 = x_1;
} else {
 lean_dec_ref(x_1);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec_ref(x_113);
x_118 = l_Lean_Meta_letToHave(x_109, x_2, x_3, x_112, x_5, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 7, 1);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_105);
lean_ctor_set(x_122, 1, x_106);
lean_ctor_set(x_122, 2, x_98);
lean_ctor_set(x_122, 3, x_107);
lean_ctor_set(x_122, 4, x_108);
lean_ctor_set(x_122, 5, x_119);
lean_ctor_set(x_122, 6, x_110);
lean_ctor_set_uint8(x_122, sizeof(void*)*7, x_100);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_116);
lean_dec_ref(x_110);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_98);
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_126 = x_118;
} else {
 lean_dec_ref(x_118);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec_ref(x_112);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_98);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_128 = lean_ctor_get(x_113, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_129 = x_113;
} else {
 lean_dec_ref(x_113);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec_ref(x_112);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_98);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_131 = lean_ctor_get(x_113, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_113, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_133 = x_113;
} else {
 lean_dec_ref(x_113);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
else
{
lean_object* x_135; 
lean_dec_ref(x_98);
lean_dec_ref(x_94);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_6);
return x_135;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_letToHaveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_4, 5);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 7);
x_16 = lean_ctor_get(x_4, 8);
x_17 = lean_ctor_get(x_4, 9);
x_18 = lean_ctor_get(x_4, 10);
x_19 = lean_ctor_get(x_4, 11);
x_20 = lean_ctor_get(x_4, 12);
x_21 = l_Lean_Elab_letToHaveValue___closed__0;
x_22 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; 
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_25 = lean_box(x_24);
if (lean_obj_tag(x_25) == 3)
{
lean_object* x_26; 
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_25);
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_ctor_get(x_1, 4);
x_33 = lean_ctor_get(x_1, 5);
x_34 = lean_ctor_get(x_1, 6);
x_35 = l_Lean_replaceRef(x_28, x_13);
lean_dec(x_13);
lean_ctor_set(x_4, 5, x_35);
x_36 = l_Lean_Meta_letToHave(x_32, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_1, 4, x_38);
lean_ctor_set(x_36, 0, x_1);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_1, 4, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_1);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
lean_dec(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_ctor_get(x_1, 2);
x_49 = lean_ctor_get(x_1, 3);
x_50 = lean_ctor_get(x_1, 4);
x_51 = lean_ctor_get(x_1, 5);
x_52 = lean_ctor_get(x_1, 6);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_53 = l_Lean_replaceRef(x_46, x_13);
lean_dec(x_13);
lean_ctor_set(x_4, 5, x_53);
x_54 = l_Lean_Meta_letToHave(x_50, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 2, x_48);
lean_ctor_set(x_58, 3, x_49);
lean_ctor_set(x_58, 4, x_55);
lean_ctor_set(x_58, 5, x_51);
lean_ctor_set(x_58, 6, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*7, x_24);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
x_66 = lean_ctor_get(x_4, 2);
x_67 = lean_ctor_get(x_4, 3);
x_68 = lean_ctor_get(x_4, 4);
x_69 = lean_ctor_get(x_4, 5);
x_70 = lean_ctor_get(x_4, 6);
x_71 = lean_ctor_get(x_4, 7);
x_72 = lean_ctor_get(x_4, 8);
x_73 = lean_ctor_get(x_4, 9);
x_74 = lean_ctor_get(x_4, 10);
x_75 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_76 = lean_ctor_get(x_4, 11);
x_77 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_78 = lean_ctor_get(x_4, 12);
lean_inc(x_78);
lean_inc(x_76);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
x_79 = l_Lean_Elab_letToHaveValue___closed__0;
x_80 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_66, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec_ref(x_78);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_6);
return x_81;
}
else
{
uint8_t x_82; lean_object* x_83; 
x_82 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_83 = lean_box(x_82);
if (lean_obj_tag(x_83) == 3)
{
lean_object* x_84; 
lean_dec_ref(x_78);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_6);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_1, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_91);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_92 = x_1;
} else {
 lean_dec_ref(x_1);
 x_92 = lean_box(0);
}
x_93 = l_Lean_replaceRef(x_85, x_69);
lean_dec(x_69);
x_94 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_94, 0, x_64);
lean_ctor_set(x_94, 1, x_65);
lean_ctor_set(x_94, 2, x_66);
lean_ctor_set(x_94, 3, x_67);
lean_ctor_set(x_94, 4, x_68);
lean_ctor_set(x_94, 5, x_93);
lean_ctor_set(x_94, 6, x_70);
lean_ctor_set(x_94, 7, x_71);
lean_ctor_set(x_94, 8, x_72);
lean_ctor_set(x_94, 9, x_73);
lean_ctor_set(x_94, 10, x_74);
lean_ctor_set(x_94, 11, x_76);
lean_ctor_set(x_94, 12, x_78);
lean_ctor_set_uint8(x_94, sizeof(void*)*13, x_75);
lean_ctor_set_uint8(x_94, sizeof(void*)*13 + 1, x_77);
x_95 = l_Lean_Meta_letToHave(x_89, x_2, x_3, x_94, x_5, x_6);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_99 = lean_alloc_ctor(0, 7, 1);
} else {
 x_99 = x_92;
}
lean_ctor_set(x_99, 0, x_85);
lean_ctor_set(x_99, 1, x_86);
lean_ctor_set(x_99, 2, x_87);
lean_ctor_set(x_99, 3, x_88);
lean_ctor_set(x_99, 4, x_96);
lean_ctor_set(x_99, 5, x_90);
lean_ctor_set(x_99, 6, x_91);
lean_ctor_set_uint8(x_99, sizeof(void*)*7, x_82);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_103 = x_95;
} else {
 lean_dec_ref(x_95);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 3);
lean_dec(x_9);
lean_ctor_set(x_6, 3, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_2);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_name_eq(x_12, x_1);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_st_ref_take(x_6, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_15, 3);
lean_dec(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_15, 3, x_21);
x_22 = lean_st_ref_set(x_6, x_15, x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_6);
x_24 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_inc(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0(x_6, x_10, x_27, x_26);
lean_dec_ref(x_27);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_25);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec_ref(x_24);
x_35 = lean_box(0);
x_36 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0(x_6, x_10, x_35, x_34);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_33);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
x_43 = lean_ctor_get(x_15, 2);
x_44 = lean_ctor_get(x_15, 4);
x_45 = lean_ctor_get(x_15, 5);
x_46 = lean_ctor_get(x_15, 6);
x_47 = lean_ctor_get(x_15, 7);
x_48 = lean_ctor_get(x_15, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_44);
lean_ctor_set(x_52, 5, x_45);
lean_ctor_set(x_52, 6, x_46);
lean_ctor_set(x_52, 7, x_47);
lean_ctor_set(x_52, 8, x_48);
x_53 = lean_st_ref_set(x_6, x_52, x_16);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec_ref(x_53);
lean_inc(x_6);
x_55 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
lean_inc(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0(x_6, x_10, x_58, x_57);
lean_dec_ref(x_58);
lean_dec(x_6);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_dec_ref(x_55);
x_65 = lean_box(0);
x_66 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0(x_6, x_10, x_65, x_64);
lean_dec(x_6);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
 lean_ctor_set_tag(x_69, 1);
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec_ref(x_10);
lean_dec(x_1);
x_70 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_11);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_100; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_15);
x_100 = l_Lean_Elab_DefKind_isTheorem(x_9);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Elab_DefKind_isExample(x_9);
x_16 = x_101;
goto block_99;
}
else
{
x_16 = x_100;
goto block_99;
}
block_99:
{
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_1, 6);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_5, 5);
x_27 = l_Lean_replaceRef(x_8, x_26);
lean_dec(x_26);
lean_ctor_set(x_5, 5, x_27);
x_28 = lean_box(x_2);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_abstractNestedProofs___boxed), 7, 2);
lean_closure_set(x_29, 0, x_14);
lean_closure_set(x_29, 1, x_28);
lean_inc(x_12);
x_30 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg(x_12, x_29, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_1, 5, x_32);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_1, 5, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_1);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
x_42 = lean_ctor_get(x_5, 2);
x_43 = lean_ctor_get(x_5, 3);
x_44 = lean_ctor_get(x_5, 4);
x_45 = lean_ctor_get(x_5, 5);
x_46 = lean_ctor_get(x_5, 6);
x_47 = lean_ctor_get(x_5, 7);
x_48 = lean_ctor_get(x_5, 8);
x_49 = lean_ctor_get(x_5, 9);
x_50 = lean_ctor_get(x_5, 10);
x_51 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_52 = lean_ctor_get(x_5, 11);
x_53 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_54 = lean_ctor_get(x_5, 12);
lean_inc(x_54);
lean_inc(x_52);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_55 = l_Lean_replaceRef(x_8, x_45);
lean_dec(x_45);
x_56 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_41);
lean_ctor_set(x_56, 2, x_42);
lean_ctor_set(x_56, 3, x_43);
lean_ctor_set(x_56, 4, x_44);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_56, 6, x_46);
lean_ctor_set(x_56, 7, x_47);
lean_ctor_set(x_56, 8, x_48);
lean_ctor_set(x_56, 9, x_49);
lean_ctor_set(x_56, 10, x_50);
lean_ctor_set(x_56, 11, x_52);
lean_ctor_set(x_56, 12, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*13, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*13 + 1, x_53);
x_57 = lean_box(x_2);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_abstractNestedProofs___boxed), 7, 2);
lean_closure_set(x_58, 0, x_14);
lean_closure_set(x_58, 1, x_57);
lean_inc(x_12);
x_59 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg(x_12, x_58, x_3, x_4, x_56, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
lean_ctor_set(x_1, 5, x_60);
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_1);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_68 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_5, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_5, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_5, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_5, 7);
lean_inc(x_75);
x_76 = lean_ctor_get(x_5, 8);
lean_inc(x_76);
x_77 = lean_ctor_get(x_5, 9);
lean_inc(x_77);
x_78 = lean_ctor_get(x_5, 10);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_80 = lean_ctor_get(x_5, 11);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_82 = lean_ctor_get(x_5, 12);
lean_inc_ref(x_82);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 lean_ctor_release(x_5, 10);
 lean_ctor_release(x_5, 11);
 lean_ctor_release(x_5, 12);
 x_83 = x_5;
} else {
 lean_dec_ref(x_5);
 x_83 = lean_box(0);
}
x_84 = l_Lean_replaceRef(x_8, x_73);
lean_dec(x_73);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 13, 2);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_69);
lean_ctor_set(x_85, 2, x_70);
lean_ctor_set(x_85, 3, x_71);
lean_ctor_set(x_85, 4, x_72);
lean_ctor_set(x_85, 5, x_84);
lean_ctor_set(x_85, 6, x_74);
lean_ctor_set(x_85, 7, x_75);
lean_ctor_set(x_85, 8, x_76);
lean_ctor_set(x_85, 9, x_77);
lean_ctor_set(x_85, 10, x_78);
lean_ctor_set(x_85, 11, x_80);
lean_ctor_set(x_85, 12, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*13, x_79);
lean_ctor_set_uint8(x_85, sizeof(void*)*13 + 1, x_81);
x_86 = lean_box(x_2);
x_87 = lean_alloc_closure((void*)(l_Lean_Meta_abstractNestedProofs___boxed), 7, 2);
lean_closure_set(x_87, 0, x_14);
lean_closure_set(x_87, 1, x_86);
lean_inc(x_12);
x_88 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg(x_12, x_87, x_3, x_4, x_85, x_6, x_7);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_92, 0, x_8);
lean_ctor_set(x_92, 1, x_10);
lean_ctor_set(x_92, 2, x_11);
lean_ctor_set(x_92, 3, x_12);
lean_ctor_set(x_92, 4, x_13);
lean_ctor_set(x_92, 5, x_89);
lean_ctor_set(x_92, 6, x_15);
lean_ctor_set_uint8(x_92, sizeof(void*)*7, x_9);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_94 = lean_ctor_get(x_88, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_7);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_withDeclNameForAuxNaming___at___Lean_Elab_abstractNestedProofs_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Elab_abstractNestedProofs(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 3);
x_12 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_10);
lean_inc(x_8);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_10);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_replaceRef(x_7, x_12);
lean_dec(x_12);
lean_ctor_set(x_2, 5, x_16);
x_17 = l_Lean_addDecl(x_15, x_2, x_3, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 3);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
x_28 = lean_ctor_get(x_2, 4);
x_29 = lean_ctor_get(x_2, 5);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_ctor_get(x_2, 7);
x_32 = lean_ctor_get(x_2, 8);
x_33 = lean_ctor_get(x_2, 9);
x_34 = lean_ctor_get(x_2, 10);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*13);
x_36 = lean_ctor_get(x_2, 11);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get(x_2, 12);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
lean_inc_ref(x_22);
lean_inc(x_20);
lean_inc(x_21);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_20);
lean_ctor_set(x_39, 2, x_22);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_replaceRef(x_19, x_29);
lean_dec(x_29);
x_43 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_26);
lean_ctor_set(x_43, 3, x_27);
lean_ctor_set(x_43, 4, x_28);
lean_ctor_set(x_43, 5, x_42);
lean_ctor_set(x_43, 6, x_30);
lean_ctor_set(x_43, 7, x_31);
lean_ctor_set(x_43, 8, x_32);
lean_ctor_set(x_43, 9, x_33);
lean_ctor_set(x_43, 10, x_34);
lean_ctor_set(x_43, 11, x_36);
lean_ctor_set(x_43, 12, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*13, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*13 + 1, x_37);
x_44 = l_Lean_addDecl(x_41, x_43, x_3, x_4);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addAsAxiom___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addAsAxiom___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addAsAxiom(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Elab_DefKind_isTheorem(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Elab_Modifiers_isNoncomputable(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
return x_4;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_compileDecl(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_compileDecl(x_1, x_9, x_3, x_4, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg(x_1, x_2, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diagnostics", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("threshold", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proofSize", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_3 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only display proof statistics when proof has at least this number of terms", 74, 74);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_2 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_3 = lean_unsigned_to_nat(16384u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_3 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_4 = l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_5 = l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_3 = l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_4 = l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_;
x_5 = l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_76__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("occs", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ↦ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(double x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_8, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_8, x_7, x_16);
x_18 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__1;
lean_inc_ref(x_3);
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_1);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_2);
x_20 = 0;
x_21 = l_Lean_MessageData_ofConstName(x_14, x_20);
lean_inc_ref(x_4);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_4);
x_22 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Nat_reprFast(x_15);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_inc_ref(x_4);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
lean_inc_ref(x_5);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_5);
x_30 = 1;
x_31 = lean_usize_add(x_7, x_30);
x_32 = lean_array_uset(x_17, x_7, x_29);
x_7 = x_31;
x_8 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_uset(x_8, x_7, x_36);
x_38 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__1;
lean_inc_ref(x_3);
x_39 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set_float(x_39, sizeof(void*)*2, x_1);
lean_ctor_set_float(x_39, sizeof(void*)*2 + 8, x_1);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 16, x_2);
x_40 = 0;
x_41 = l_Lean_MessageData_ofConstName(x_34, x_40);
lean_inc_ref(x_4);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__3;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Nat_reprFast(x_35);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_MessageData_ofFormat(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
lean_inc_ref(x_4);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
lean_inc_ref(x_5);
x_50 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_5);
x_51 = 1;
x_52 = lean_usize_add(x_7, x_51);
x_53 = lean_array_uset(x_37, x_7, x_50);
x_7 = x_52;
x_8 = x_53;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0(double x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = 0;
x_9 = l_Lean_log___at___Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2_spec__2_spec__2___redArg(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_diagnostics_threshold_proofSize;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics_threshold;
return x_1;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("theorem", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_isDiagnosticsEnabled___redArg(x_6, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec_ref(x_9);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
lean_inc_ref(x_21);
x_23 = l_Lean_Expr_numObjs(x_21, x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0;
x_29 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_27, x_28);
x_30 = lean_nat_dec_lt(x_29, x_25);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_25);
lean_free_object(x_1);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_6);
x_31 = lean_box(0);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_free_object(x_23);
x_32 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1;
x_33 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_27, x_32);
lean_dec(x_27);
x_34 = l_Lean_Expr_numApps(x_21, x_33, x_26);
lean_dec(x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; double x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2;
x_39 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_40 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3;
x_41 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4;
x_42 = lean_array_size(x_36);
x_43 = 0;
x_44 = lean_unbox(x_10);
x_45 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(x_38, x_44, x_39, x_40, x_41, x_42, x_43, x_36, x_37);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 2);
lean_dec(x_51);
x_52 = lean_ctor_get(x_20, 1);
lean_dec(x_52);
x_53 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6;
x_54 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set_float(x_54, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_54, sizeof(void*)*2 + 8, x_38);
x_55 = lean_unbox(x_10);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 16, x_55);
x_56 = l_Nat_reprFast(x_25);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_58);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_40);
lean_ctor_set(x_34, 0, x_45);
lean_ctor_set_tag(x_20, 9);
lean_ctor_set(x_20, 2, x_41);
lean_ctor_set(x_20, 1, x_34);
lean_ctor_set(x_20, 0, x_54);
x_59 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8;
x_60 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_39);
lean_ctor_set_float(x_60, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_60, sizeof(void*)*2 + 8, x_38);
x_61 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 16, x_61);
x_62 = l_Lean_MessageData_ofName(x_50);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_40);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_40);
x_65 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9;
x_66 = lean_array_push(x_65, x_20);
x_67 = l_Array_append___redArg(x_66, x_48);
lean_dec(x_48);
lean_ctor_set_tag(x_1, 9);
lean_ctor_set(x_1, 2, x_67);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_60);
x_68 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_1, x_4, x_5, x_6, x_7, x_49);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_69 = lean_ctor_get(x_45, 0);
x_70 = lean_ctor_get(x_45, 1);
x_71 = lean_ctor_get(x_20, 0);
lean_inc(x_71);
lean_dec(x_20);
x_72 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6;
x_73 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_39);
lean_ctor_set_float(x_73, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_73, sizeof(void*)*2 + 8, x_38);
x_74 = lean_unbox(x_10);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 16, x_74);
x_75 = l_Nat_reprFast(x_25);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_MessageData_ofFormat(x_76);
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_77);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_40);
lean_ctor_set(x_34, 0, x_45);
x_78 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_34);
lean_ctor_set(x_78, 2, x_41);
x_79 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8;
x_80 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_39);
lean_ctor_set_float(x_80, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_80, sizeof(void*)*2 + 8, x_38);
x_81 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_80, sizeof(void*)*2 + 16, x_81);
x_82 = l_Lean_MessageData_ofName(x_71);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_40);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_40);
x_85 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9;
x_86 = lean_array_push(x_85, x_78);
x_87 = l_Array_append___redArg(x_86, x_69);
lean_dec(x_69);
lean_ctor_set_tag(x_1, 9);
lean_ctor_set(x_1, 2, x_87);
lean_ctor_set(x_1, 1, x_84);
lean_ctor_set(x_1, 0, x_80);
x_88 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_1, x_4, x_5, x_6, x_7, x_70);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_89 = lean_ctor_get(x_45, 0);
x_90 = lean_ctor_get(x_45, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_45);
x_91 = lean_ctor_get(x_20, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_92 = x_20;
} else {
 lean_dec_ref(x_20);
 x_92 = lean_box(0);
}
x_93 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6;
x_94 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_39);
lean_ctor_set_float(x_94, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_94, sizeof(void*)*2 + 8, x_38);
x_95 = lean_unbox(x_10);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 16, x_95);
x_96 = l_Nat_reprFast(x_25);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_MessageData_ofFormat(x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_40);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_40);
lean_ctor_set(x_34, 0, x_99);
if (lean_is_scalar(x_92)) {
 x_100 = lean_alloc_ctor(9, 3, 0);
} else {
 x_100 = x_92;
 lean_ctor_set_tag(x_100, 9);
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_34);
lean_ctor_set(x_100, 2, x_41);
x_101 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8;
x_102 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_39);
lean_ctor_set_float(x_102, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_102, sizeof(void*)*2 + 8, x_38);
x_103 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 16, x_103);
x_104 = l_Lean_MessageData_ofName(x_91);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_40);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_40);
x_107 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9;
x_108 = lean_array_push(x_107, x_100);
x_109 = l_Array_append___redArg(x_108, x_89);
lean_dec(x_89);
lean_ctor_set_tag(x_1, 9);
lean_ctor_set(x_1, 2, x_109);
lean_ctor_set(x_1, 1, x_106);
lean_ctor_set(x_1, 0, x_102);
x_110 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_1, x_4, x_5, x_6, x_7, x_90);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; double x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; size_t x_117; size_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_111 = lean_ctor_get(x_34, 0);
x_112 = lean_ctor_get(x_34, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_34);
x_113 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2;
x_114 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_115 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3;
x_116 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4;
x_117 = lean_array_size(x_111);
x_118 = 0;
x_119 = lean_unbox(x_10);
x_120 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(x_113, x_119, x_114, x_115, x_116, x_117, x_118, x_111, x_112);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_20, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_125 = x_20;
} else {
 lean_dec_ref(x_20);
 x_125 = lean_box(0);
}
x_126 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6;
x_127 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_114);
lean_ctor_set_float(x_127, sizeof(void*)*2, x_113);
lean_ctor_set_float(x_127, sizeof(void*)*2 + 8, x_113);
x_128 = lean_unbox(x_10);
lean_ctor_set_uint8(x_127, sizeof(void*)*2 + 16, x_128);
x_129 = l_Nat_reprFast(x_25);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Lean_MessageData_ofFormat(x_130);
if (lean_is_scalar(x_123)) {
 x_132 = lean_alloc_ctor(7, 2, 0);
} else {
 x_132 = x_123;
 lean_ctor_set_tag(x_132, 7);
}
lean_ctor_set(x_132, 0, x_115);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_115);
if (lean_is_scalar(x_125)) {
 x_134 = lean_alloc_ctor(9, 3, 0);
} else {
 x_134 = x_125;
 lean_ctor_set_tag(x_134, 9);
}
lean_ctor_set(x_134, 0, x_127);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_116);
x_135 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8;
x_136 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_114);
lean_ctor_set_float(x_136, sizeof(void*)*2, x_113);
lean_ctor_set_float(x_136, sizeof(void*)*2 + 8, x_113);
x_137 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_136, sizeof(void*)*2 + 16, x_137);
x_138 = l_Lean_MessageData_ofName(x_124);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_115);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_115);
x_141 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9;
x_142 = lean_array_push(x_141, x_134);
x_143 = l_Array_append___redArg(x_142, x_121);
lean_dec(x_121);
lean_ctor_set_tag(x_1, 9);
lean_ctor_set(x_1, 2, x_143);
lean_ctor_set(x_1, 1, x_140);
lean_ctor_set(x_1, 0, x_136);
x_144 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_1, x_4, x_5, x_6, x_7, x_122);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_23, 0);
x_146 = lean_ctor_get(x_23, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_23);
x_147 = lean_ctor_get(x_6, 2);
lean_inc(x_147);
x_148 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0;
x_149 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_147, x_148);
x_150 = lean_nat_dec_lt(x_149, x_145);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_147);
lean_dec(x_145);
lean_free_object(x_1);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_6);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_146);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; double x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; size_t x_163; size_t x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_153 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1;
x_154 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_147, x_153);
lean_dec(x_147);
x_155 = l_Lean_Expr_numApps(x_21, x_154, x_146);
lean_dec(x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2;
x_160 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_161 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3;
x_162 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4;
x_163 = lean_array_size(x_156);
x_164 = 0;
x_165 = lean_unbox(x_10);
x_166 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(x_159, x_165, x_160, x_161, x_162, x_163, x_164, x_156, x_157);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_20, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_171 = x_20;
} else {
 lean_dec_ref(x_20);
 x_171 = lean_box(0);
}
x_172 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6;
x_173 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_160);
lean_ctor_set_float(x_173, sizeof(void*)*2, x_159);
lean_ctor_set_float(x_173, sizeof(void*)*2 + 8, x_159);
x_174 = lean_unbox(x_10);
lean_ctor_set_uint8(x_173, sizeof(void*)*2 + 16, x_174);
x_175 = l_Nat_reprFast(x_145);
x_176 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l_Lean_MessageData_ofFormat(x_176);
if (lean_is_scalar(x_169)) {
 x_178 = lean_alloc_ctor(7, 2, 0);
} else {
 x_178 = x_169;
 lean_ctor_set_tag(x_178, 7);
}
lean_ctor_set(x_178, 0, x_161);
lean_ctor_set(x_178, 1, x_177);
if (lean_is_scalar(x_158)) {
 x_179 = lean_alloc_ctor(7, 2, 0);
} else {
 x_179 = x_158;
 lean_ctor_set_tag(x_179, 7);
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_161);
if (lean_is_scalar(x_171)) {
 x_180 = lean_alloc_ctor(9, 3, 0);
} else {
 x_180 = x_171;
 lean_ctor_set_tag(x_180, 9);
}
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_180, 2, x_162);
x_181 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8;
x_182 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_160);
lean_ctor_set_float(x_182, sizeof(void*)*2, x_159);
lean_ctor_set_float(x_182, sizeof(void*)*2 + 8, x_159);
x_183 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_182, sizeof(void*)*2 + 16, x_183);
x_184 = l_Lean_MessageData_ofName(x_170);
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_161);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_161);
x_187 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9;
x_188 = lean_array_push(x_187, x_180);
x_189 = l_Array_append___redArg(x_188, x_167);
lean_dec(x_167);
lean_ctor_set_tag(x_1, 9);
lean_ctor_set(x_1, 2, x_189);
lean_ctor_set(x_1, 1, x_186);
lean_ctor_set(x_1, 0, x_182);
x_190 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_1, x_4, x_5, x_6, x_7, x_168);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_191 = lean_ctor_get(x_1, 0);
x_192 = lean_ctor_get(x_1, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_1);
lean_inc_ref(x_192);
x_193 = l_Lean_Expr_numObjs(x_192, x_18);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_6, 2);
lean_inc(x_197);
x_198 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0;
x_199 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_197, x_198);
x_200 = lean_nat_dec_lt(x_199, x_194);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_197);
lean_dec(x_194);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_10);
lean_dec_ref(x_6);
x_201 = lean_box(0);
if (lean_is_scalar(x_196)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_196;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_195);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; double x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; size_t x_213; size_t x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_196);
x_203 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1;
x_204 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_197, x_203);
lean_dec(x_197);
x_205 = l_Lean_Expr_numApps(x_192, x_204, x_195);
lean_dec(x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2;
x_210 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_211 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3;
x_212 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4;
x_213 = lean_array_size(x_206);
x_214 = 0;
x_215 = lean_unbox(x_10);
x_216 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(x_209, x_215, x_210, x_211, x_212, x_213, x_214, x_206, x_207);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_219 = x_216;
} else {
 lean_dec_ref(x_216);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_191, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 lean_ctor_release(x_191, 2);
 x_221 = x_191;
} else {
 lean_dec_ref(x_191);
 x_221 = lean_box(0);
}
x_222 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6;
x_223 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_210);
lean_ctor_set_float(x_223, sizeof(void*)*2, x_209);
lean_ctor_set_float(x_223, sizeof(void*)*2 + 8, x_209);
x_224 = lean_unbox(x_10);
lean_ctor_set_uint8(x_223, sizeof(void*)*2 + 16, x_224);
x_225 = l_Nat_reprFast(x_194);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = l_Lean_MessageData_ofFormat(x_226);
if (lean_is_scalar(x_219)) {
 x_228 = lean_alloc_ctor(7, 2, 0);
} else {
 x_228 = x_219;
 lean_ctor_set_tag(x_228, 7);
}
lean_ctor_set(x_228, 0, x_211);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_208)) {
 x_229 = lean_alloc_ctor(7, 2, 0);
} else {
 x_229 = x_208;
 lean_ctor_set_tag(x_229, 7);
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_211);
if (lean_is_scalar(x_221)) {
 x_230 = lean_alloc_ctor(9, 3, 0);
} else {
 x_230 = x_221;
 lean_ctor_set_tag(x_230, 9);
}
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_230, 2, x_212);
x_231 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8;
x_232 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_210);
lean_ctor_set_float(x_232, sizeof(void*)*2, x_209);
lean_ctor_set_float(x_232, sizeof(void*)*2 + 8, x_209);
x_233 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_232, sizeof(void*)*2 + 16, x_233);
x_234 = l_Lean_MessageData_ofName(x_220);
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_211);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_211);
x_237 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9;
x_238 = lean_array_push(x_237, x_230);
x_239 = l_Array_append___redArg(x_238, x_217);
lean_dec(x_217);
x_240 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_240, 0, x_232);
lean_ctor_set(x_240, 1, x_236);
lean_ctor_set(x_240, 2, x_239);
x_241 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_240, x_4, x_5, x_6, x_7, x_218);
return x_241;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
double x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_11 = lean_unbox(x_2);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg(x_10, x_11, x_3, x_4, x_5, x_12, x_13, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
double x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_17 = lean_unbox(x_2);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0(x_16, x_17, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logInfo___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; uint8_t x_21; 
x_20 = lean_st_ref_get(x_3, x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_92; size_t x_96; size_t x_97; lean_object* x_98; lean_object* x_99; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Expr_hash(x_2);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_96 = lean_usize_sub(x_34, x_35);
x_97 = lean_usize_land(x_33, x_96);
x_98 = lean_array_uget(x_24, x_97);
lean_dec_ref(x_24);
x_99 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(x_2, x_98);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_free_object(x_20);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_100 = lean_apply_8(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_110; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
x_110 = lean_unbox(x_101);
lean_dec(x_101);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_111 = lean_box(0);
x_36 = x_111;
x_37 = x_102;
goto block_91;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_113);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_114 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
x_92 = x_116;
goto block_95;
}
else
{
lean_dec_ref(x_113);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_92 = x_114;
goto block_95;
}
}
case 6:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_118);
x_103 = x_117;
x_104 = x_118;
x_105 = x_3;
goto block_109;
}
case 7:
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_120);
x_103 = x_119;
x_104 = x_120;
x_105 = x_3;
goto block_109;
}
case 8:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_123);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_124 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec_ref(x_124);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_126 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_123, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_127);
x_92 = x_128;
goto block_95;
}
else
{
lean_dec_ref(x_123);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_92 = x_126;
goto block_95;
}
}
else
{
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_92 = x_124;
goto block_95;
}
}
case 10:
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_129);
x_130 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_129, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
x_92 = x_130;
goto block_95;
}
case 11:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_131);
x_132 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_131, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
x_92 = x_132;
goto block_95;
}
default: 
{
lean_object* x_133; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_133 = lean_box(0);
x_36 = x_133;
x_37 = x_102;
goto block_91;
}
}
}
block_109:
{
lean_object* x_106; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_106 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_103, x_105, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_104, x_105, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
x_92 = x_108;
goto block_95;
}
else
{
lean_dec_ref(x_104);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_92 = x_106;
goto block_95;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_134 = !lean_is_exclusive(x_100);
if (x_134 == 0)
{
return x_100;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_100, 0);
x_136 = lean_ctor_get(x_100, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_100);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_138 = lean_ctor_get(x_99, 0);
lean_inc(x_138);
lean_dec_ref(x_99);
lean_ctor_set(x_20, 0, x_138);
return x_20;
}
block_91:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_st_ref_take(x_3, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = lean_usize_sub(x_45, x_35);
x_47 = lean_usize_land(x_33, x_46);
x_48 = lean_array_uget(x_43, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_2, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_42, x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_52, 2, x_48);
x_53 = lean_array_uset(x_43, x_47, x_52);
x_54 = lean_unsigned_to_nat(4u);
x_55 = lean_nat_mul(x_51, x_54);
x_56 = lean_unsigned_to_nat(3u);
x_57 = lean_nat_div(x_55, x_56);
lean_dec(x_55);
x_58 = lean_array_get_size(x_53);
x_59 = lean_nat_dec_le(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_53);
lean_ctor_set(x_39, 1, x_60);
lean_ctor_set(x_39, 0, x_51);
x_11 = x_36;
x_12 = x_40;
x_13 = x_39;
goto block_19;
}
else
{
lean_ctor_set(x_39, 1, x_53);
lean_ctor_set(x_39, 0, x_51);
x_11 = x_36;
x_12 = x_40;
x_13 = x_39;
goto block_19;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_box(0);
x_62 = lean_array_uset(x_43, x_47, x_61);
x_63 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_2, x_36, x_48);
x_64 = lean_array_uset(x_62, x_47, x_63);
lean_ctor_set(x_39, 1, x_64);
x_11 = x_36;
x_12 = x_40;
x_13 = x_39;
goto block_19;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; size_t x_69; size_t x_70; lean_object* x_71; uint8_t x_72; 
x_65 = lean_ctor_get(x_39, 0);
x_66 = lean_ctor_get(x_39, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_39);
x_67 = lean_array_get_size(x_66);
x_68 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_69 = lean_usize_sub(x_68, x_35);
x_70 = lean_usize_land(x_33, x_69);
x_71 = lean_array_uget(x_66, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_2, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_65, x_73);
lean_dec(x_65);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_36);
lean_ctor_set(x_75, 2, x_71);
x_76 = lean_array_uset(x_66, x_70, x_75);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_nat_mul(x_74, x_77);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_nat_div(x_78, x_79);
lean_dec(x_78);
x_81 = lean_array_get_size(x_76);
x_82 = lean_nat_dec_le(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_83);
x_11 = x_36;
x_12 = x_40;
x_13 = x_84;
goto block_19;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_76);
x_11 = x_36;
x_12 = x_40;
x_13 = x_85;
goto block_19;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_box(0);
x_87 = lean_array_uset(x_66, x_70, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_2, x_36, x_71);
x_89 = lean_array_uset(x_87, x_70, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_65);
lean_ctor_set(x_90, 1, x_89);
x_11 = x_36;
x_12 = x_40;
x_13 = x_90;
goto block_19;
}
}
}
block_95:
{
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_36 = x_93;
x_37 = x_94;
goto block_91;
}
else
{
lean_dec_ref(x_2);
return x_92;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; size_t x_150; size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_186; size_t x_190; size_t x_191; lean_object* x_192; lean_object* x_193; 
x_139 = lean_ctor_get(x_20, 0);
x_140 = lean_ctor_get(x_20, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_20);
x_141 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_141);
lean_dec(x_139);
x_142 = lean_array_get_size(x_141);
x_143 = l_Lean_Expr_hash(x_2);
x_144 = 32;
x_145 = lean_uint64_shift_right(x_143, x_144);
x_146 = lean_uint64_xor(x_143, x_145);
x_147 = 16;
x_148 = lean_uint64_shift_right(x_146, x_147);
x_149 = lean_uint64_xor(x_146, x_148);
x_150 = lean_uint64_to_usize(x_149);
x_151 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_152 = 1;
x_190 = lean_usize_sub(x_151, x_152);
x_191 = lean_usize_land(x_150, x_190);
x_192 = lean_array_uget(x_141, x_191);
lean_dec_ref(x_141);
x_193 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(x_2, x_192);
lean_dec(x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_2);
x_194 = lean_apply_8(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_140);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_204; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec_ref(x_194);
x_204 = lean_unbox(x_195);
lean_dec(x_195);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_205 = lean_box(0);
x_153 = x_205;
x_154 = x_196;
goto block_185;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_207);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_208 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_206, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_196);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_207, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_209);
x_186 = x_210;
goto block_189;
}
else
{
lean_dec_ref(x_207);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_186 = x_208;
goto block_189;
}
}
case 6:
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_212);
x_197 = x_211;
x_198 = x_212;
x_199 = x_3;
goto block_203;
}
case 7:
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_214);
x_197 = x_213;
x_198 = x_214;
x_199 = x_3;
goto block_203;
}
case 8:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_215);
x_216 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_216);
x_217 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_217);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_218 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_215, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_196);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec_ref(x_218);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_220 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_216, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_217, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_221);
x_186 = x_222;
goto block_189;
}
else
{
lean_dec_ref(x_217);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_186 = x_220;
goto block_189;
}
}
else
{
lean_dec_ref(x_217);
lean_dec_ref(x_216);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_186 = x_218;
goto block_189;
}
}
case 10:
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_223);
x_224 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_223, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_196);
x_186 = x_224;
goto block_189;
}
case 11:
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_225);
x_226 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_225, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_196);
x_186 = x_226;
goto block_189;
}
default: 
{
lean_object* x_227; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_227 = lean_box(0);
x_153 = x_227;
x_154 = x_196;
goto block_185;
}
}
}
block_203:
{
lean_object* x_200; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_200 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_197, x_199, x_4, x_5, x_6, x_7, x_8, x_9, x_196);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_198, x_199, x_4, x_5, x_6, x_7, x_8, x_9, x_201);
x_186 = x_202;
goto block_189;
}
else
{
lean_dec_ref(x_198);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_186 = x_200;
goto block_189;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_228 = lean_ctor_get(x_194, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_194, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_230 = x_194;
} else {
 lean_dec_ref(x_194);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_232 = lean_ctor_get(x_193, 0);
lean_inc(x_232);
lean_dec_ref(x_193);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_140);
return x_233;
}
block_185:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; size_t x_164; lean_object* x_165; uint8_t x_166; 
x_155 = lean_st_ref_take(x_3, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec_ref(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc_ref(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
x_161 = lean_array_get_size(x_159);
x_162 = lean_usize_of_nat(x_161);
lean_dec(x_161);
x_163 = lean_usize_sub(x_162, x_152);
x_164 = lean_usize_land(x_150, x_163);
x_165 = lean_array_uget(x_159, x_164);
x_166 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelMVars_visitExpr_spec__0___redArg(x_2, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_add(x_158, x_167);
lean_dec(x_158);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_2);
lean_ctor_set(x_169, 1, x_153);
lean_ctor_set(x_169, 2, x_165);
x_170 = lean_array_uset(x_159, x_164, x_169);
x_171 = lean_unsigned_to_nat(4u);
x_172 = lean_nat_mul(x_168, x_171);
x_173 = lean_unsigned_to_nat(3u);
x_174 = lean_nat_div(x_172, x_173);
lean_dec(x_172);
x_175 = lean_array_get_size(x_170);
x_176 = lean_nat_dec_le(x_174, x_175);
lean_dec(x_175);
lean_dec(x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelMVars_visitExpr_spec__1___redArg(x_170);
if (lean_is_scalar(x_160)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_160;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_177);
x_11 = x_153;
x_12 = x_157;
x_13 = x_178;
goto block_19;
}
else
{
lean_object* x_179; 
if (lean_is_scalar(x_160)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_160;
}
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_170);
x_11 = x_153;
x_12 = x_157;
x_13 = x_179;
goto block_19;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_box(0);
x_181 = lean_array_uset(x_159, x_164, x_180);
x_182 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_2, x_153, x_165);
x_183 = lean_array_uset(x_181, x_164, x_182);
if (lean_is_scalar(x_160)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_160;
}
lean_ctor_set(x_184, 0, x_158);
lean_ctor_set(x_184, 1, x_183);
x_11 = x_153;
x_12 = x_157;
x_13 = x_184;
goto block_19;
}
}
block_189:
{
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec_ref(x_186);
x_153 = x_187;
x_154 = x_188;
goto block_185;
}
else
{
lean_dec_ref(x_2);
return x_186;
}
}
}
block_19:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_set(x_3, x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid meta definition, '", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' must be `meta` to access", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid definition, may not access `meta` declaration '", 55, 55);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_21; 
x_21 = l_Lean_Expr_isAutoParam(x_3);
if (x_21 == 0)
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = lean_st_ref_get(x_9, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_27);
lean_dec(x_25);
lean_inc(x_22);
x_28 = lean_get_ir_phases(x_27, x_22);
switch (x_28) {
case 0:
{
uint8_t x_29; 
x_29 = l_Lean_Elab_Modifiers_isMeta(x_2);
if (x_29 == 0)
{
lean_free_object(x_23);
lean_dec(x_22);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_26;
goto block_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec_ref(x_1);
x_30 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__1;
x_31 = l_Lean_MessageData_ofConstName(x_22, x_21);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_31);
lean_ctor_set(x_23, 0, x_30);
x_32 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__3;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 1:
{
uint8_t x_39; 
x_39 = l_Lean_Elab_Modifiers_isMeta(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec_ref(x_1);
x_40 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__5;
x_41 = l_Lean_MessageData_ofConstName(x_22, x_39);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_41);
lean_ctor_set(x_23, 0, x_40);
x_42 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__7;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_free_object(x_23);
lean_dec(x_22);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_26;
goto block_20;
}
}
default: 
{
lean_free_object(x_23);
lean_dec(x_22);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_26;
goto block_20;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_23, 0);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_23);
x_51 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_51);
lean_dec(x_49);
lean_inc(x_22);
x_52 = lean_get_ir_phases(x_51, x_22);
switch (x_52) {
case 0:
{
uint8_t x_53; 
x_53 = l_Lean_Elab_Modifiers_isMeta(x_2);
if (x_53 == 0)
{
lean_dec(x_22);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_50;
goto block_20;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_1);
x_54 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__1;
x_55 = l_Lean_MessageData_ofConstName(x_22, x_21);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__3;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_58, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
case 1:
{
uint8_t x_64; 
x_64 = l_Lean_Elab_Modifiers_isMeta(x_2);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_1);
x_65 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__5;
x_66 = l_Lean_MessageData_ofConstName(x_22, x_64);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__7;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_69, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_dec(x_22);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_50;
goto block_20;
}
}
default: 
{
lean_dec(x_22);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_9;
x_17 = x_50;
goto block_20;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_3);
x_75 = lean_box(0);
x_76 = lean_apply_8(x_1, x_75, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_76;
}
}
else
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_10);
return x_79;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_apply_8(x_1, x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__6;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__0___boxed), 8, 0);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___boxed), 10, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_13);
x_17 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_16, x_14, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_st_ref_get(x_11, x_19);
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_dec(x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_ForEachExpr_visit___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc_ref(x_3);
x_10 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_checkNotAlreadyDeclared___at___Lean_Elab_applyVisibility___at___Lean_Elab_mkDeclName___at___Lean_Elab_expandDeclId___at___Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3_spec__3_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = 1;
x_17 = l_Lean_Elab_Term_addTermInfo_x27(x_2, x_11, x_13, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__7;
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__6;
x_3 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__5;
x_4 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__4;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_1, 0);
lean_inc(x_295);
x_296 = !lean_is_exclusive(x_11);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_11, 5);
x_298 = l_Lean_replaceRef(x_295, x_297);
lean_dec(x_297);
lean_dec(x_295);
lean_ctor_set(x_11, 5, x_298);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_299 = l_Lean_Elab_abstractNestedProofs(x_1, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec_ref(x_299);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_302 = l_Lean_Elab_letToHaveType(x_300, x_9, x_10, x_11, x_12, x_301);
if (lean_obj_tag(x_302) == 0)
{
if (x_6 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec_ref(x_302);
x_231 = x_303;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_11;
x_237 = x_12;
x_238 = x_304;
goto block_294;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_302, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_302, 1);
lean_inc(x_306);
lean_dec_ref(x_302);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_307 = l_Lean_Elab_letToHaveValue(x_305, x_9, x_10, x_11, x_12, x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec_ref(x_307);
x_231 = x_308;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_11;
x_237 = x_12;
x_238 = x_309;
goto block_294;
}
else
{
uint8_t x_310; 
lean_dec_ref(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
x_310 = !lean_is_exclusive(x_307);
if (x_310 == 0)
{
return x_307;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_307, 0);
x_312 = lean_ctor_get(x_307, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_307);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
}
else
{
uint8_t x_314; 
lean_dec_ref(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
x_314 = !lean_is_exclusive(x_302);
if (x_314 == 0)
{
return x_302;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_302, 0);
x_316 = lean_ctor_get(x_302, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_302);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
uint8_t x_318; 
lean_dec_ref(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
x_318 = !lean_is_exclusive(x_299);
if (x_318 == 0)
{
return x_299;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_299, 0);
x_320 = lean_ctor_get(x_299, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_299);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_322 = lean_ctor_get(x_11, 0);
x_323 = lean_ctor_get(x_11, 1);
x_324 = lean_ctor_get(x_11, 2);
x_325 = lean_ctor_get(x_11, 3);
x_326 = lean_ctor_get(x_11, 4);
x_327 = lean_ctor_get(x_11, 5);
x_328 = lean_ctor_get(x_11, 6);
x_329 = lean_ctor_get(x_11, 7);
x_330 = lean_ctor_get(x_11, 8);
x_331 = lean_ctor_get(x_11, 9);
x_332 = lean_ctor_get(x_11, 10);
x_333 = lean_ctor_get_uint8(x_11, sizeof(void*)*13);
x_334 = lean_ctor_get(x_11, 11);
x_335 = lean_ctor_get_uint8(x_11, sizeof(void*)*13 + 1);
x_336 = lean_ctor_get(x_11, 12);
lean_inc(x_336);
lean_inc(x_334);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_11);
x_337 = l_Lean_replaceRef(x_295, x_327);
lean_dec(x_327);
lean_dec(x_295);
x_338 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_338, 0, x_322);
lean_ctor_set(x_338, 1, x_323);
lean_ctor_set(x_338, 2, x_324);
lean_ctor_set(x_338, 3, x_325);
lean_ctor_set(x_338, 4, x_326);
lean_ctor_set(x_338, 5, x_337);
lean_ctor_set(x_338, 6, x_328);
lean_ctor_set(x_338, 7, x_329);
lean_ctor_set(x_338, 8, x_330);
lean_ctor_set(x_338, 9, x_331);
lean_ctor_set(x_338, 10, x_332);
lean_ctor_set(x_338, 11, x_334);
lean_ctor_set(x_338, 12, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*13, x_333);
lean_ctor_set_uint8(x_338, sizeof(void*)*13 + 1, x_335);
lean_inc(x_12);
lean_inc_ref(x_338);
lean_inc(x_10);
lean_inc_ref(x_9);
x_339 = l_Lean_Elab_abstractNestedProofs(x_1, x_5, x_9, x_10, x_338, x_12, x_13);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec_ref(x_339);
lean_inc(x_12);
lean_inc_ref(x_338);
lean_inc(x_10);
lean_inc_ref(x_9);
x_342 = l_Lean_Elab_letToHaveType(x_340, x_9, x_10, x_338, x_12, x_341);
if (lean_obj_tag(x_342) == 0)
{
if (x_6 == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec_ref(x_342);
x_231 = x_343;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_338;
x_237 = x_12;
x_238 = x_344;
goto block_294;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
lean_dec_ref(x_342);
lean_inc(x_12);
lean_inc_ref(x_338);
lean_inc(x_10);
lean_inc_ref(x_9);
x_347 = l_Lean_Elab_letToHaveValue(x_345, x_9, x_10, x_338, x_12, x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec_ref(x_347);
x_231 = x_348;
x_232 = x_7;
x_233 = x_8;
x_234 = x_9;
x_235 = x_10;
x_236 = x_338;
x_237 = x_12;
x_238 = x_349;
goto block_294;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec_ref(x_338);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
x_350 = lean_ctor_get(x_347, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_352 = x_347;
} else {
 lean_dec_ref(x_347);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec_ref(x_338);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_342, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_356 = x_342;
} else {
 lean_dec_ref(x_342);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec_ref(x_338);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
x_358 = lean_ctor_get(x_339, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_339, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_360 = x_339;
} else {
 lean_dec_ref(x_339);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
block_31:
{
if (x_4 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_20);
lean_inc(x_15);
x_25 = l_Lean_enableRealizationsForConst(x_15, x_20, x_21, x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
x_27 = l_Lean_Meta_generateEagerEqns(x_15, x_18, x_19, x_20, x_21, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = 1;
x_30 = l_Lean_Elab_applyAttributesOf(x_14, x_29, x_16, x_17, x_18, x_19, x_20, x_21, x_28);
lean_dec_ref(x_14);
return x_30;
}
else
{
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
return x_27;
}
}
}
block_49:
{
lean_object* x_43; 
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc_ref(x_35);
x_43 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta(x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42);
if (lean_obj_tag(x_43) == 0)
{
if (x_2 == 0)
{
lean_object* x_44; 
lean_dec_ref(x_35);
lean_dec(x_32);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_14 = x_33;
x_15 = x_34;
x_16 = x_36;
x_17 = x_37;
x_18 = x_38;
x_19 = x_39;
x_20 = x_40;
x_21 = x_41;
x_22 = x_44;
goto block_31;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_35);
lean_dec_ref(x_35);
if (x_46 == 0)
{
lean_dec(x_32);
x_14 = x_33;
x_15 = x_34;
x_16 = x_36;
x_17 = x_37;
x_18 = x_38;
x_19 = x_39;
x_20 = x_40;
x_21 = x_41;
x_22 = x_45;
goto block_31;
}
else
{
lean_object* x_47; 
lean_inc(x_41);
lean_inc_ref(x_40);
x_47 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg(x_32, x_36, x_40, x_41, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_14 = x_33;
x_15 = x_34;
x_16 = x_36;
x_17 = x_37;
x_18 = x_38;
x_19 = x_39;
x_20 = x_40;
x_21 = x_41;
x_22 = x_48;
goto block_31;
}
else
{
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_34);
lean_dec_ref(x_33);
return x_47;
}
}
}
}
else
{
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
return x_43;
}
}
block_176:
{
lean_object* x_62; 
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_54);
x_62 = l_Lean_addDecl(x_54, x_59, x_60, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
x_64 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0___redArg(x_50, x_55, x_56, x_57, x_58, x_59, x_60, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__0;
lean_inc_ref(x_53);
x_67 = lean_array_push(x_66, x_53);
x_68 = 0;
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc_ref(x_55);
x_69 = l_Lean_Elab_applyAttributesOf(x_67, x_68, x_55, x_56, x_57, x_58, x_59, x_60, x_65);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = lean_ctor_get_uint8(x_51, sizeof(void*)*3 + 1);
lean_dec_ref(x_51);
switch (x_70) {
case 0:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_32 = x_54;
x_33 = x_67;
x_34 = x_52;
x_35 = x_53;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
x_41 = x_60;
x_42 = x_71;
goto block_49;
}
case 1:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec_ref(x_69);
x_73 = lean_st_ref_take(x_60, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 5);
lean_dec(x_78);
lean_inc(x_52);
x_79 = l_Lean_addMeta(x_77, x_52);
x_80 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
lean_ctor_set(x_74, 5, x_80);
lean_ctor_set(x_74, 0, x_79);
x_81 = lean_st_ref_set(x_60, x_74, x_75);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_st_ref_take(x_58, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_84, 1);
lean_dec(x_87);
x_88 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8;
lean_ctor_set(x_84, 1, x_88);
x_89 = lean_st_ref_set(x_58, x_84, x_85);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec_ref(x_89);
x_32 = x_54;
x_33 = x_67;
x_34 = x_52;
x_35 = x_53;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
x_41 = x_60;
x_42 = x_90;
goto block_49;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_84, 0);
x_92 = lean_ctor_get(x_84, 2);
x_93 = lean_ctor_get(x_84, 3);
x_94 = lean_ctor_get(x_84, 4);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_84);
x_95 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8;
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_92);
lean_ctor_set(x_96, 3, x_93);
lean_ctor_set(x_96, 4, x_94);
x_97 = lean_st_ref_set(x_58, x_96, x_85);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_32 = x_54;
x_33 = x_67;
x_34 = x_52;
x_35 = x_53;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
x_41 = x_60;
x_42 = x_98;
goto block_49;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_99 = lean_ctor_get(x_74, 0);
x_100 = lean_ctor_get(x_74, 1);
x_101 = lean_ctor_get(x_74, 2);
x_102 = lean_ctor_get(x_74, 3);
x_103 = lean_ctor_get(x_74, 4);
x_104 = lean_ctor_get(x_74, 6);
x_105 = lean_ctor_get(x_74, 7);
x_106 = lean_ctor_get(x_74, 8);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_74);
lean_inc(x_52);
x_107 = l_Lean_addMeta(x_99, x_52);
x_108 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
x_109 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_101);
lean_ctor_set(x_109, 3, x_102);
lean_ctor_set(x_109, 4, x_103);
lean_ctor_set(x_109, 5, x_108);
lean_ctor_set(x_109, 6, x_104);
lean_ctor_set(x_109, 7, x_105);
lean_ctor_set(x_109, 8, x_106);
x_110 = lean_st_ref_set(x_60, x_109, x_75);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_st_ref_take(x_58, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec_ref(x_112);
x_115 = lean_ctor_get(x_113, 0);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_113, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 3);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_113, 4);
lean_inc_ref(x_118);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_119 = x_113;
} else {
 lean_dec_ref(x_113);
 x_119 = lean_box(0);
}
x_120 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8;
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 5, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_116);
lean_ctor_set(x_121, 3, x_117);
lean_ctor_set(x_121, 4, x_118);
x_122 = lean_st_ref_set(x_58, x_121, x_114);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec_ref(x_122);
x_32 = x_54;
x_33 = x_67;
x_34 = x_52;
x_35 = x_53;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
x_41 = x_60;
x_42 = x_123;
goto block_49;
}
}
default: 
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = lean_ctor_get(x_69, 1);
lean_inc(x_124);
lean_dec_ref(x_69);
x_125 = lean_st_ref_take(x_60, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = !lean_is_exclusive(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_129 = lean_ctor_get(x_126, 0);
x_130 = lean_ctor_get(x_126, 5);
lean_dec(x_130);
lean_inc(x_52);
x_131 = l_Lean_addNoncomputable(x_129, x_52);
x_132 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
lean_ctor_set(x_126, 5, x_132);
lean_ctor_set(x_126, 0, x_131);
x_133 = lean_st_ref_set(x_60, x_126, x_127);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_st_ref_take(x_58, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec_ref(x_135);
x_138 = !lean_is_exclusive(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_136, 1);
lean_dec(x_139);
x_140 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8;
lean_ctor_set(x_136, 1, x_140);
x_141 = lean_st_ref_set(x_58, x_136, x_137);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec_ref(x_141);
x_32 = x_54;
x_33 = x_67;
x_34 = x_52;
x_35 = x_53;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
x_41 = x_60;
x_42 = x_142;
goto block_49;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_136, 0);
x_144 = lean_ctor_get(x_136, 2);
x_145 = lean_ctor_get(x_136, 3);
x_146 = lean_ctor_get(x_136, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_136);
x_147 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8;
x_148 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set(x_148, 4, x_146);
x_149 = lean_st_ref_set(x_58, x_148, x_137);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec_ref(x_149);
x_32 = x_54;
x_33 = x_67;
x_34 = x_52;
x_35 = x_53;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
x_41 = x_60;
x_42 = x_150;
goto block_49;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_151 = lean_ctor_get(x_126, 0);
x_152 = lean_ctor_get(x_126, 1);
x_153 = lean_ctor_get(x_126, 2);
x_154 = lean_ctor_get(x_126, 3);
x_155 = lean_ctor_get(x_126, 4);
x_156 = lean_ctor_get(x_126, 6);
x_157 = lean_ctor_get(x_126, 7);
x_158 = lean_ctor_get(x_126, 8);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_126);
lean_inc(x_52);
x_159 = l_Lean_addNoncomputable(x_151, x_52);
x_160 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
x_161 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_152);
lean_ctor_set(x_161, 2, x_153);
lean_ctor_set(x_161, 3, x_154);
lean_ctor_set(x_161, 4, x_155);
lean_ctor_set(x_161, 5, x_160);
lean_ctor_set(x_161, 6, x_156);
lean_ctor_set(x_161, 7, x_157);
lean_ctor_set(x_161, 8, x_158);
x_162 = lean_st_ref_set(x_60, x_161, x_127);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_st_ref_take(x_58, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_165, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 3);
lean_inc_ref(x_169);
x_170 = lean_ctor_get(x_165, 4);
lean_inc_ref(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 lean_ctor_release(x_165, 4);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
x_172 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8;
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 5, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_168);
lean_ctor_set(x_173, 3, x_169);
lean_ctor_set(x_173, 4, x_170);
x_174 = lean_st_ref_set(x_58, x_173, x_166);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec_ref(x_174);
x_32 = x_54;
x_33 = x_67;
x_34 = x_52;
x_35 = x_53;
x_36 = x_55;
x_37 = x_56;
x_38 = x_57;
x_39 = x_58;
x_40 = x_59;
x_41 = x_60;
x_42 = x_175;
goto block_49;
}
}
}
}
else
{
lean_dec_ref(x_67);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
return x_69;
}
}
else
{
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
return x_64;
}
}
else
{
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
return x_62;
}
}
block_194:
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_179);
lean_ctor_set(x_192, 2, x_181);
lean_ctor_set(x_192, 3, x_3);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_191);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_50 = x_177;
x_51 = x_186;
x_52 = x_183;
x_53 = x_182;
x_54 = x_193;
x_55 = x_184;
x_56 = x_189;
x_57 = x_185;
x_58 = x_188;
x_59 = x_178;
x_60 = x_180;
x_61 = x_187;
goto block_176;
}
block_212:
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_197);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_3);
lean_ctor_set_uint8(x_210, sizeof(void*)*4, x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_50 = x_195;
x_51 = x_204;
x_52 = x_201;
x_53 = x_200;
x_54 = x_211;
x_55 = x_202;
x_56 = x_207;
x_57 = x_203;
x_58 = x_206;
x_59 = x_196;
x_60 = x_198;
x_61 = x_199;
goto block_176;
}
block_230:
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_215);
lean_ctor_set(x_228, 2, x_224);
lean_ctor_set(x_228, 3, x_3);
lean_ctor_set_uint8(x_228, sizeof(void*)*4, x_227);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_50 = x_213;
x_51 = x_222;
x_52 = x_219;
x_53 = x_218;
x_54 = x_229;
x_55 = x_220;
x_56 = x_225;
x_57 = x_221;
x_58 = x_223;
x_59 = x_214;
x_60 = x_217;
x_61 = x_216;
goto block_176;
}
block_294:
{
lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_231, 0);
lean_inc(x_239);
x_240 = lean_ctor_get_uint8(x_231, sizeof(void*)*7);
x_241 = lean_ctor_get(x_231, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_231, 2);
lean_inc_ref(x_242);
x_243 = lean_ctor_get(x_231, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_231, 4);
lean_inc_ref(x_244);
x_245 = lean_ctor_get(x_231, 5);
lean_inc_ref(x_245);
lean_inc(x_243);
x_246 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lam__0), 9, 2);
lean_closure_set(x_246, 0, x_243);
lean_closure_set(x_246, 1, x_239);
lean_inc_ref(x_244);
lean_inc(x_243);
x_247 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_247, 0, x_243);
lean_ctor_set(x_247, 1, x_241);
lean_ctor_set(x_247, 2, x_244);
lean_inc(x_3);
lean_inc_ref(x_245);
lean_inc_ref(x_247);
x_248 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
lean_ctor_set(x_248, 2, x_3);
x_249 = lean_box(x_240);
switch (lean_obj_tag(x_249)) {
case 1:
{
lean_object* x_250; 
lean_inc(x_237);
lean_inc_ref(x_236);
lean_inc(x_235);
lean_inc_ref(x_234);
x_250 = l_Lean_Meta_isProp(x_244, x_234, x_235, x_236, x_237, x_238);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_unbox(x_251);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; uint32_t x_259; uint32_t x_260; uint32_t x_261; lean_object* x_262; 
lean_dec_ref(x_248);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
lean_dec_ref(x_250);
x_254 = lean_st_ref_get(x_237, x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec_ref(x_254);
x_257 = lean_ctor_get(x_255, 0);
lean_inc_ref(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get_uint8(x_242, sizeof(void*)*3 + 3);
lean_inc_ref(x_245);
x_259 = l_Lean_getMaxHeight(x_257, x_245);
x_260 = 1;
x_261 = lean_uint32_add(x_259, x_260);
x_262 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_262, 0, x_261);
if (x_258 == 0)
{
uint8_t x_263; 
x_263 = 1;
x_213 = x_246;
x_214 = x_236;
x_215 = x_245;
x_216 = x_256;
x_217 = x_237;
x_218 = x_231;
x_219 = x_243;
x_220 = x_232;
x_221 = x_234;
x_222 = x_242;
x_223 = x_235;
x_224 = x_262;
x_225 = x_233;
x_226 = x_247;
x_227 = x_263;
goto block_230;
}
else
{
uint8_t x_264; 
x_264 = 0;
x_213 = x_246;
x_214 = x_236;
x_215 = x_245;
x_216 = x_256;
x_217 = x_237;
x_218 = x_231;
x_219 = x_243;
x_220 = x_232;
x_221 = x_234;
x_222 = x_242;
x_223 = x_235;
x_224 = x_262;
x_225 = x_233;
x_226 = x_247;
x_227 = x_264;
goto block_230;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec_ref(x_247);
lean_dec_ref(x_245);
lean_dec(x_3);
x_265 = lean_ctor_get(x_250, 1);
lean_inc(x_265);
lean_dec_ref(x_250);
lean_inc_ref(x_236);
lean_inc_ref(x_248);
x_266 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag(x_248, x_232, x_233, x_234, x_235, x_236, x_237, x_265);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_268, 0, x_248);
x_50 = x_246;
x_51 = x_242;
x_52 = x_243;
x_53 = x_231;
x_54 = x_268;
x_55 = x_232;
x_56 = x_233;
x_57 = x_234;
x_58 = x_235;
x_59 = x_236;
x_60 = x_237;
x_61 = x_267;
goto block_176;
}
}
else
{
uint8_t x_269; 
lean_dec_ref(x_248);
lean_dec_ref(x_247);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec(x_243);
lean_dec_ref(x_242);
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec_ref(x_232);
lean_dec_ref(x_231);
lean_dec(x_3);
x_269 = !lean_is_exclusive(x_250);
if (x_269 == 0)
{
return x_250;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_250, 0);
x_271 = lean_ctor_get(x_250, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_250);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
case 2:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec_ref(x_247);
lean_dec_ref(x_245);
lean_dec_ref(x_244);
lean_dec(x_3);
lean_inc_ref(x_236);
lean_inc_ref(x_248);
x_273 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag(x_248, x_232, x_233, x_234, x_235, x_236, x_237, x_238);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec_ref(x_273);
x_275 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_275, 0, x_248);
x_50 = x_246;
x_51 = x_242;
x_52 = x_243;
x_53 = x_231;
x_54 = x_275;
x_55 = x_232;
x_56 = x_233;
x_57 = x_234;
x_58 = x_235;
x_59 = x_236;
x_60 = x_237;
x_61 = x_274;
goto block_176;
}
case 4:
{
uint8_t x_276; lean_object* x_277; lean_object* x_278; 
lean_dec_ref(x_248);
lean_dec_ref(x_244);
x_276 = lean_ctor_get_uint8(x_242, sizeof(void*)*3 + 3);
x_277 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_277, 0, x_247);
lean_ctor_set(x_277, 1, x_245);
lean_ctor_set(x_277, 2, x_3);
lean_ctor_set_uint8(x_277, sizeof(void*)*3, x_276);
x_278 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_50 = x_246;
x_51 = x_242;
x_52 = x_243;
x_53 = x_231;
x_54 = x_278;
x_55 = x_232;
x_56 = x_233;
x_57 = x_234;
x_58 = x_235;
x_59 = x_236;
x_60 = x_237;
x_61 = x_238;
goto block_176;
}
case 5:
{
uint8_t x_279; lean_object* x_280; 
lean_dec_ref(x_248);
lean_dec_ref(x_244);
x_279 = lean_ctor_get_uint8(x_242, sizeof(void*)*3 + 3);
x_280 = lean_box(1);
if (x_279 == 0)
{
uint8_t x_281; 
x_281 = 1;
x_195 = x_246;
x_196 = x_236;
x_197 = x_245;
x_198 = x_237;
x_199 = x_238;
x_200 = x_231;
x_201 = x_243;
x_202 = x_232;
x_203 = x_234;
x_204 = x_242;
x_205 = x_280;
x_206 = x_235;
x_207 = x_233;
x_208 = x_247;
x_209 = x_281;
goto block_212;
}
else
{
uint8_t x_282; 
x_282 = 0;
x_195 = x_246;
x_196 = x_236;
x_197 = x_245;
x_198 = x_237;
x_199 = x_238;
x_200 = x_231;
x_201 = x_243;
x_202 = x_232;
x_203 = x_234;
x_204 = x_242;
x_205 = x_280;
x_206 = x_235;
x_207 = x_233;
x_208 = x_247;
x_209 = x_282;
goto block_212;
}
}
default: 
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; uint32_t x_288; uint32_t x_289; uint32_t x_290; lean_object* x_291; 
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec_ref(x_244);
x_283 = lean_st_ref_get(x_237, x_238);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec_ref(x_283);
x_286 = lean_ctor_get(x_284, 0);
lean_inc_ref(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get_uint8(x_242, sizeof(void*)*3 + 3);
lean_inc_ref(x_245);
x_288 = l_Lean_getMaxHeight(x_286, x_245);
x_289 = 1;
x_290 = lean_uint32_add(x_288, x_289);
x_291 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_291, 0, x_290);
if (x_287 == 0)
{
uint8_t x_292; 
x_292 = 1;
x_177 = x_246;
x_178 = x_236;
x_179 = x_245;
x_180 = x_237;
x_181 = x_291;
x_182 = x_231;
x_183 = x_243;
x_184 = x_232;
x_185 = x_234;
x_186 = x_242;
x_187 = x_285;
x_188 = x_235;
x_189 = x_233;
x_190 = x_247;
x_191 = x_292;
goto block_194;
}
else
{
uint8_t x_293; 
x_293 = 0;
x_177 = x_246;
x_178 = x_236;
x_179 = x_245;
x_180 = x_237;
x_181 = x_291;
x_182 = x_231;
x_183 = x_243;
x_184 = x_232;
x_185 = x_234;
x_186 = x_242;
x_187 = x_285;
x_188 = x_235;
x_189 = x_233;
x_190 = x_247;
x_191 = x_293;
goto block_194;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_4);
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_14, x_3, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_11, x_2, x_11, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Elab_addAndCompileNonRec(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_13, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Elab_addNonRec(x_1, x_13, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___closed__0;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; 
x_9 = l_Lean_hasRecAppSyntax(x_1);
if (x_9 == 0)
{
x_5 = x_1;
goto block_8;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Expr_mdataExpr_x21(x_1);
lean_dec_ref(x_1);
x_5 = x_10;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Elab_eraseRecAppSyntaxExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hasRecAppSyntax___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___closed__0;
x_6 = lean_find_expr(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lam__1___boxed), 4, 0);
x_10 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_8, x_9, x_2, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
x_12 = lean_ctor_get(x_1, 6);
x_13 = l_Lean_Elab_eraseRecAppSyntaxExpr(x_11, x_2, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_1, 5, x_15);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_1, 5, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
x_28 = lean_ctor_get(x_1, 4);
x_29 = lean_ctor_get(x_1, 5);
x_30 = lean_ctor_get(x_1, 6);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_1);
x_31 = l_Lean_Elab_eraseRecAppSyntaxExpr(x_29, x_2, x_3, x_4);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_27);
lean_ctor_set(x_35, 4, x_28);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*7, x_24);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_30);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_23);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_3, x_2);
lean_inc(x_5);
lean_inc_ref(x_4);
x_10 = l_Lean_Elab_eraseRecAppSyntax(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_14, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___redArg(x_1, x_2, x_3, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Elab_addAndCompileUnsafe_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_List_reverse___redArg(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_9, 5);
lean_inc_ref(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_13);
x_16 = lean_box(0);
lean_inc(x_2);
x_17 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_2);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_1);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_17);
{
lean_object* _tmp_2 = x_10;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_19, 5);
lean_inc_ref(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_23);
x_26 = lean_box(0);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_1);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_3 = x_20;
x_4 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg(x_1, x_2, x_3, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_addAndCompileUnsafe_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc_ref(x_6);
x_18 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_checkNotAlreadyDeclared___at___Lean_Elab_applyVisibility___at___Lean_Elab_mkDeclName___at___Lean_Elab_expandDeclId___at___Lean_Elab_Term_expandDeclId_spec__0_spec__1_spec__3_spec__3_spec__3(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_24 = l_Lean_Elab_Term_addTermInfo_x27(x_16, x_19, x_21, x_22, x_23, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
{
size_t _tmp_3 = x_27;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_11 = x_25;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_24;
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lam__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_addAndCompileUnsafe_spec__3(x_1, x_2, x_3, x_4, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_addAndCompileUnsafe___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_array_size(x_1);
x_11 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___redArg(x_10, x_11, x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Elab_instInhabitedPreDefinition;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_13, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_7, 5);
lean_inc(x_13);
x_21 = lean_array_to_list(x_13);
x_22 = lean_box(0);
lean_inc(x_21);
x_23 = l_List_mapTR_loop___at___Lean_Elab_addAndCompileUnsafe_spec__1(x_21, x_22);
x_24 = lean_box(0);
x_25 = l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg(x_2, x_23, x_21, x_24, x_14);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_replaceRef(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
lean_ctor_set(x_7, 5, x_28);
x_29 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_29, 0, x_26);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_29);
x_30 = l_Lean_addDecl(x_29, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_box(0);
x_33 = lean_array_size(x_13);
x_34 = lean_box_usize(x_33);
x_35 = l_Lean_Elab_addAndCompileUnsafe___boxed__const__1;
lean_inc(x_13);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_addAndCompileUnsafe___lam__0___boxed), 11, 4);
lean_closure_set(x_36, 0, x_32);
lean_closure_set(x_36, 1, x_13);
lean_closure_set(x_36, 2, x_34);
lean_closure_set(x_36, 3, x_35);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_37 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0___redArg(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_40 = l_Lean_Elab_applyAttributesOf(x_13, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc(x_8);
lean_inc_ref(x_7);
x_42 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg(x_29, x_3, x_7, x_8, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = 1;
x_45 = l_Lean_Elab_applyAttributesOf(x_13, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_13);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_32);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
return x_45;
}
}
else
{
lean_dec_ref(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_42;
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_40;
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_37;
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_30;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_7, 1);
x_52 = lean_ctor_get(x_7, 2);
x_53 = lean_ctor_get(x_7, 3);
x_54 = lean_ctor_get(x_7, 4);
x_55 = lean_ctor_get(x_7, 5);
x_56 = lean_ctor_get(x_7, 6);
x_57 = lean_ctor_get(x_7, 7);
x_58 = lean_ctor_get(x_7, 8);
x_59 = lean_ctor_get(x_7, 9);
x_60 = lean_ctor_get(x_7, 10);
x_61 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_62 = lean_ctor_get(x_7, 11);
x_63 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_64 = lean_ctor_get(x_7, 12);
lean_inc(x_64);
lean_inc(x_62);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_7);
lean_inc(x_13);
x_65 = lean_array_to_list(x_13);
x_66 = lean_box(0);
lean_inc(x_65);
x_67 = l_List_mapTR_loop___at___Lean_Elab_addAndCompileUnsafe_spec__1(x_65, x_66);
x_68 = lean_box(0);
x_69 = l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg(x_2, x_67, x_65, x_68, x_14);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_replaceRef(x_18, x_55);
lean_dec(x_55);
lean_dec(x_18);
x_73 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_73, 0, x_50);
lean_ctor_set(x_73, 1, x_51);
lean_ctor_set(x_73, 2, x_52);
lean_ctor_set(x_73, 3, x_53);
lean_ctor_set(x_73, 4, x_54);
lean_ctor_set(x_73, 5, x_72);
lean_ctor_set(x_73, 6, x_56);
lean_ctor_set(x_73, 7, x_57);
lean_ctor_set(x_73, 8, x_58);
lean_ctor_set(x_73, 9, x_59);
lean_ctor_set(x_73, 10, x_60);
lean_ctor_set(x_73, 11, x_62);
lean_ctor_set(x_73, 12, x_64);
lean_ctor_set_uint8(x_73, sizeof(void*)*13, x_61);
lean_ctor_set_uint8(x_73, sizeof(void*)*13 + 1, x_63);
x_74 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_74, 0, x_70);
lean_inc(x_8);
lean_inc_ref(x_73);
lean_inc_ref(x_74);
x_75 = l_Lean_addDecl(x_74, x_73, x_8, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_box(0);
x_78 = lean_array_size(x_13);
x_79 = lean_box_usize(x_78);
x_80 = l_Lean_Elab_addAndCompileUnsafe___boxed__const__1;
lean_inc(x_13);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_addAndCompileUnsafe___lam__0___boxed), 11, 4);
lean_closure_set(x_81, 0, x_77);
lean_closure_set(x_81, 1, x_13);
lean_closure_set(x_81, 2, x_79);
lean_closure_set(x_81, 3, x_80);
lean_inc(x_8);
lean_inc_ref(x_73);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_82 = l_Lean_Elab_withSaveInfoContext___at___Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo_spec__0___redArg(x_81, x_3, x_4, x_5, x_6, x_73, x_8, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = 0;
lean_inc(x_8);
lean_inc_ref(x_73);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_85 = l_Lean_Elab_applyAttributesOf(x_13, x_84, x_3, x_4, x_5, x_6, x_73, x_8, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
lean_inc(x_8);
lean_inc_ref(x_73);
x_87 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___redArg(x_74, x_3, x_73, x_8, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = 1;
x_90 = l_Lean_Elab_applyAttributesOf(x_13, x_89, x_3, x_4, x_5, x_6, x_73, x_8, x_88);
lean_dec(x_13);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
return x_90;
}
}
else
{
lean_dec_ref(x_73);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_87;
}
}
else
{
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_85;
}
}
else
{
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_82;
}
}
else
{
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_75;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_94 = !lean_is_exclusive(x_12);
if (x_94 == 0)
{
return x_12;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_12, 0);
x_96 = lean_ctor_get(x_12, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_12);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompileUnsafe_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_List_mapM_loop___at___Lean_Elab_addAndCompileUnsafe_spec__2(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_addAndCompileUnsafe_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_addAndCompileUnsafe_spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Lean_Elab_addAndCompileUnsafe___lam__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_Elab_addAndCompileUnsafe(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompilePartialRec_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_6, 3);
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_4, x_3, x_11);
x_13 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_14 = l_Lean_Compiler_mkUnsafeRecName(x_8);
x_15 = lean_replace_expr(x_1, x_9);
lean_dec_ref(x_9);
lean_ctor_set(x_6, 5, x_15);
lean_ctor_set(x_6, 3, x_14);
lean_ctor_set(x_6, 2, x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_12, x_3, x_6);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_6);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_uset(x_4, x_3, x_27);
x_29 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_30 = l_Lean_Compiler_mkUnsafeRecName(x_23);
x_31 = lean_replace_expr(x_1, x_25);
lean_dec_ref(x_25);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_24);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_21);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_35 = lean_array_uset(x_28, x_3, x_32);
x_3 = x_34;
x_4 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 7);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_1);
x_11 = lean_st_ref_set(x_2, x_5, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_1);
lean_ctor_set(x_5, 7, x_21);
x_22 = lean_st_ref_set(x_2, x_5, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
x_29 = lean_ctor_get(x_5, 2);
x_30 = lean_ctor_get(x_5, 3);
x_31 = lean_ctor_get(x_5, 4);
x_32 = lean_ctor_get(x_5, 5);
x_33 = lean_ctor_get(x_5, 6);
x_34 = lean_ctor_get(x_5, 8);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_35 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_37);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 x_38 = x_6;
} else {
 lean_dec_ref(x_6);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 3, 1);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_36);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_1);
x_40 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_29);
lean_ctor_set(x_40, 3, x_30);
lean_ctor_set(x_40, 4, x_31);
lean_ctor_set(x_40, 5, x_32);
lean_ctor_set(x_40, 6, x_33);
lean_ctor_set(x_40, 7, x_39);
lean_ctor_set(x_40, 8, x_34);
x_41 = lean_st_ref_set(x_2, x_40, x_7);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg(x_1, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 7);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
lean_dec_ref(x_12);
x_15 = l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg(x_1, x_8, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_8);
x_17 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg(x_14, x_8, x_19);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec_ref(x_17);
x_27 = l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg(x_14, x_8, x_26);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_addAndCompilePartialRec_spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 1;
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_6);
lean_dec_ref(x_6);
if (x_7 == 0)
{
return x_5;
}
else
{
if (x_4 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_5;
}
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_nat_dec_lt(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
if (x_7 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_2);
x_12 = l_Array_anyMUnsafe_any___at___Lean_Elab_fixLevelParams_spec__0(x_5, x_3, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Compiler_mkUnsafeRecName(x_5);
x_15 = l_Lean_Expr_const___override(x_14, x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_4);
x_17 = lean_box(0);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_21; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_1);
lean_inc_ref(x_1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_addAndCompilePartialRec___lam__0___boxed), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_1);
x_21 = lean_nat_dec_lt(x_9, x_10);
if (x_21 == 0)
{
lean_dec(x_10);
goto block_20;
}
else
{
if (x_21 == 0)
{
lean_dec(x_10);
goto block_20;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_24 = l_Array_anyMUnsafe_any___at___Lean_Elab_addAndCompilePartialRec_spec__3(x_1, x_22, x_23);
if (x_24 == 0)
{
goto block_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
block_20:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = 0;
x_13 = lean_array_size(x_1);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompilePartialRec_spec__0(x_11, x_13, x_14, x_1);
lean_dec_ref(x_11);
x_16 = 2;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_addAndCompileUnsafe___boxed), 9, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___redArg(x_12, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompilePartialRec_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_addAndCompilePartialRec_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___redArg(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Elab_enableInfoTree___at___Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1_spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___redArg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Elab_withEnableInfoTree___at___Lean_Elab_addAndCompilePartialRec_spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_addAndCompilePartialRec_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Elab_addAndCompilePartialRec_spec__3(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addAndCompilePartialRec___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConst(x_2);
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_constName_x21(x_2);
x_5 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_find_expr(x_3, x_2);
lean_dec_ref(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec_ref(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_ensureNoRecFn___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected occurrence of recursive application", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ensureNoRecFn___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ensureNoRecFn___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_getAppFn(x_2);
x_19 = l_Lean_Expr_isConst(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
x_8 = x_19;
goto block_17;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_constName_x21(x_18);
lean_dec_ref(x_18);
x_21 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_1, x_20);
lean_dec(x_20);
x_8 = x_21;
goto block_17;
}
block_17:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Elab_ensureNoRecFn___lam__0___closed__1;
x_12 = l_Lean_indentExpr(x_2);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc_ref(x_1);
x_8 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_ensureNoRecFn___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5(x_2, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_ensureNoRecFn___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_checkCodomainsLevel_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_ctor_get(x_12, 5);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_13, x_1, x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_19, x_3, x_16);
x_3 = x_21;
x_4 = x_22;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_sanitizeNames;
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid mutual definition, result types must be in the same universe ", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("level, resulting type ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__6;
x_2 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("for `", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("and for `", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_15 = l_Lean_Meta_getLevel(x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_18 = l_Lean_Meta_isLevelDefEq(x_1, x_16, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_109; uint8_t x_134; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_st_ref_get(x_13, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_12, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_12, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_12, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_12, 6);
lean_inc(x_31);
x_32 = lean_ctor_get(x_12, 7);
lean_inc(x_32);
x_33 = lean_ctor_get(x_12, 8);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 9);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 10);
lean_inc(x_35);
x_36 = lean_ctor_get(x_12, 11);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_12, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get(x_12, 12);
lean_inc_ref(x_38);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 lean_ctor_release(x_12, 9);
 lean_ctor_release(x_12, 10);
 lean_ctor_release(x_12, 11);
 lean_ctor_release(x_12, 12);
 x_39 = x_12;
} else {
 lean_dec_ref(x_12);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_40);
lean_dec(x_23);
x_41 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__0;
x_42 = lean_unbox(x_19);
lean_dec(x_19);
x_43 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_28, x_41, x_42);
x_44 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__1;
x_45 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_43, x_44);
x_134 = l_Lean_Kernel_isDiagnosticsEnabled(x_40);
lean_dec_ref(x_40);
if (x_134 == 0)
{
if (x_45 == 0)
{
x_46 = x_26;
x_47 = x_27;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
x_52 = x_33;
x_53 = x_34;
x_54 = x_35;
x_55 = x_36;
x_56 = x_37;
x_57 = x_38;
x_58 = x_13;
x_59 = x_24;
goto block_108;
}
else
{
x_109 = x_134;
goto block_133;
}
}
else
{
x_109 = x_45;
goto block_133;
}
block_108:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__2;
x_61 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_43, x_60);
if (lean_is_scalar(x_39)) {
 x_62 = lean_alloc_ctor(0, 13, 2);
} else {
 x_62 = x_39;
}
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_47);
lean_ctor_set(x_62, 2, x_43);
lean_ctor_set(x_62, 3, x_48);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_49);
lean_ctor_set(x_62, 6, x_50);
lean_ctor_set(x_62, 7, x_51);
lean_ctor_set(x_62, 8, x_52);
lean_ctor_set(x_62, 9, x_53);
lean_ctor_set(x_62, 10, x_54);
lean_ctor_set(x_62, 11, x_55);
lean_ctor_set(x_62, 12, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*13, x_45);
lean_ctor_set_uint8(x_62, sizeof(void*)*13 + 1, x_56);
lean_inc(x_58);
lean_inc_ref(x_62);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_2);
x_63 = lean_infer_type(x_2, x_10, x_11, x_62, x_58, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
lean_inc(x_58);
lean_inc_ref(x_62);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_66 = lean_infer_type(x_9, x_10, x_11, x_62, x_58, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_ctor_get(x_3, 3);
lean_inc(x_69);
lean_dec_ref(x_3);
x_70 = lean_array_get(x_4, x_5, x_6);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__7;
x_73 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__9;
x_74 = l_Lean_MessageData_ofName(x_69);
if (lean_is_scalar(x_25)) {
 x_75 = lean_alloc_ctor(7, 2, 0);
} else {
 x_75 = x_25;
 lean_ctor_set_tag(x_75, 7);
}
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__11;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_indentExpr(x_2);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__13;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofExpr(x_64);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__15;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_72);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__17;
x_88 = l_Lean_MessageData_ofName(x_71);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_76);
x_91 = l_Lean_indentExpr(x_9);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_80);
x_94 = l_Lean_MessageData_ofExpr(x_67);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_86);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_98, x_10, x_11, x_62, x_58, x_68);
lean_dec(x_58);
lean_dec_ref(x_62);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_64);
lean_dec_ref(x_62);
lean_dec(x_58);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_100 = !lean_is_exclusive(x_66);
if (x_100 == 0)
{
return x_66;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_66, 0);
x_102 = lean_ctor_get(x_66, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_66);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_62);
lean_dec(x_58);
lean_dec(x_25);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_104 = !lean_is_exclusive(x_63);
if (x_104 == 0)
{
return x_63;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_63, 0);
x_106 = lean_ctor_get(x_63, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_63);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
block_133:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_st_ref_take(x_13, x_24);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 5);
lean_dec(x_115);
x_116 = l_Lean_Kernel_enableDiag(x_114, x_45);
x_117 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
lean_ctor_set(x_111, 5, x_117);
lean_ctor_set(x_111, 0, x_116);
x_118 = lean_st_ref_set(x_13, x_111, x_112);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec_ref(x_118);
x_46 = x_26;
x_47 = x_27;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
x_52 = x_33;
x_53 = x_34;
x_54 = x_35;
x_55 = x_36;
x_56 = x_37;
x_57 = x_38;
x_58 = x_13;
x_59 = x_119;
goto block_108;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_120 = lean_ctor_get(x_111, 0);
x_121 = lean_ctor_get(x_111, 1);
x_122 = lean_ctor_get(x_111, 2);
x_123 = lean_ctor_get(x_111, 3);
x_124 = lean_ctor_get(x_111, 4);
x_125 = lean_ctor_get(x_111, 6);
x_126 = lean_ctor_get(x_111, 7);
x_127 = lean_ctor_get(x_111, 8);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_128 = l_Lean_Kernel_enableDiag(x_120, x_45);
x_129 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3;
x_130 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_121);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_123);
lean_ctor_set(x_130, 4, x_124);
lean_ctor_set(x_130, 5, x_129);
lean_ctor_set(x_130, 6, x_125);
lean_ctor_set(x_130, 7, x_126);
lean_ctor_set(x_130, 8, x_127);
x_131 = lean_st_ref_set(x_13, x_130, x_112);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec_ref(x_131);
x_46 = x_26;
x_47 = x_27;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
x_52 = x_33;
x_53 = x_34;
x_54 = x_35;
x_55 = x_36;
x_56 = x_37;
x_57 = x_38;
x_58 = x_13;
x_59 = x_132;
goto block_108;
}
}
else
{
x_46 = x_26;
x_47 = x_27;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
x_51 = x_32;
x_52 = x_33;
x_53 = x_34;
x_54 = x_35;
x_55 = x_36;
x_56 = x_37;
x_57 = x_38;
x_58 = x_13;
x_59 = x_24;
goto block_108;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_135 = !lean_is_exclusive(x_18);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_18, 0);
lean_dec(x_136);
lean_ctor_set(x_18, 0, x_7);
return x_18;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_18, 1);
lean_inc(x_137);
lean_dec(x_18);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_7);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_139 = !lean_is_exclusive(x_18);
if (x_139 == 0)
{
return x_18;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_18, 0);
x_141 = lean_ctor_get(x_18, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_18);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_15);
if (x_143 == 0)
{
return x_15;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_15, 0);
x_145 = lean_ctor_get(x_15, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_15);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_array_fget(x_5, x_10);
x_17 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
lean_inc(x_10);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_10);
lean_closure_set(x_18, 6, x_6);
lean_inc(x_7);
x_19 = lean_array_get(x_7, x_8, x_10);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_22 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_17, x_20, x_18, x_21, x_21, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_10, x_26);
lean_dec(x_10);
x_28 = lean_nat_dec_lt(x_27, x_9);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_free_object(x_22);
x_10 = x_27;
x_15 = x_24;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_10, x_31);
lean_dec(x_10);
x_33 = lean_nat_dec_lt(x_32, x_9);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
x_10 = x_32;
x_15 = x_30;
goto _start;
}
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; 
x_24 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_16, x_19, x_20, x_21, x_22, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_array_fget(x_5, x_12);
x_19 = lean_ctor_get(x_18, 4);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
lean_inc(x_12);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_12);
lean_closure_set(x_20, 6, x_6);
lean_inc(x_7);
x_21 = lean_array_get(x_7, x_8, x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = 0;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_24 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_19, x_22, x_20, x_23, x_23, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_12, x_28);
lean_dec(x_12);
x_30 = lean_nat_dec_lt(x_29, x_10);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_31; 
lean_free_object(x_24);
x_31 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_29, x_13, x_14, x_15, x_16, x_26);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_12, x_33);
lean_dec(x_12);
x_35 = lean_nat_dec_lt(x_34, x_10);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_34, x_13, x_14, x_15, x_16, x_32);
return x_37;
}
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; 
x_24 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_14, x_16, x_19, x_20, x_21, x_22, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_15 = l_Lean_Meta_getLevel(x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(0);
x_20 = lean_nat_dec_lt(x_1, x_2);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
uint8_t x_21; lean_object* x_22; 
lean_free_object(x_15);
x_21 = 0;
lean_inc(x_1);
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg(x_17, x_9, x_3, x_4, x_5, x_19, x_6, x_7, x_21, x_2, x_1, x_1, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
return x_22;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_box(0);
x_30 = lean_nat_dec_lt(x_1, x_2);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
lean_inc(x_1);
x_33 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg(x_27, x_9, x_3, x_4, x_5, x_29, x_6, x_7, x_32, x_2, x_1, x_1, x_10, x_11, x_12, x_13, x_28);
lean_dec(x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
return x_33;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_checkCodomainsLevel___lam__0___boxed), 7, 0);
x_11 = lean_array_size(x_1);
x_12 = 0;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_checkCodomainsLevel_spec__0(x_10, x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Elab_instInhabitedPreDefinition;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_16, x_1, x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc_ref(x_19);
lean_inc(x_14);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_checkCodomainsLevel___lam__1___boxed), 14, 7);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_7);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_16);
lean_closure_set(x_20, 4, x_1);
lean_closure_set(x_20, 5, x_17);
lean_closure_set(x_20, 6, x_14);
x_21 = lean_array_get(x_17, x_14, x_17);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_19, x_22, x_20, x_9, x_9, x_2, x_3, x_4, x_5, x_15);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_checkCodomainsLevel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_checkCodomainsLevel_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; lean_object* x_25; 
x_24 = lean_unbox(x_9);
x_25 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_8);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_9);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; lean_object* x_25; 
x_24 = lean_unbox(x_9);
x_25 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_8);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_checkCodomainsLevel___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkCodomainsLevel___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_checkCodomainsLevel___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 4);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 5);
lean_inc_ref(x_10);
lean_dec_ref(x_8);
x_11 = lean_array_push(x_4, x_9);
x_12 = lean_array_push(x_11, x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___redArg(x_1, x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_8, 5);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 4);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mul(x_12, x_6);
lean_inc_ref(x_2);
x_14 = lean_array_get(x_2, x_3, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_13, x_15);
lean_dec(x_13);
lean_inc_ref(x_2);
x_17 = lean_array_get(x_2, x_3, x_16);
lean_dec(x_16);
lean_ctor_set(x_8, 5, x_17);
lean_ctor_set(x_8, 4, x_14);
x_18 = lean_array_push(x_5, x_8);
x_19 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_20 = lean_nat_dec_lt(x_19, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec_ref(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
else
{
x_5 = x_18;
x_6 = x_19;
goto _start;
}
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get_uint8(x_8, sizeof(void*)*7);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_8);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_nat_mul(x_29, x_6);
lean_inc_ref(x_2);
x_31 = lean_array_get(x_2, x_3, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_30, x_32);
lean_dec(x_30);
lean_inc_ref(x_2);
x_34 = lean_array_get(x_2, x_3, x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_27);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*7, x_24);
x_36 = lean_array_push(x_5, x_35);
x_37 = lean_nat_add(x_6, x_32);
lean_dec(x_6);
x_38 = lean_nat_dec_lt(x_37, x_4);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec_ref(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
else
{
x_5 = x_36;
x_6 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg(x_1, x_2, x_3, x_8, x_10, x_11, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_stringToMessageData(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___redArg(x_1, x_2, x_3, x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_array_get_size(x_1);
x_15 = lean_mk_empty_array_with_capacity(x_5);
x_16 = lean_nat_dec_lt(x_5, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
x_17 = lean_sharecommon_quick(x_12);
lean_dec(x_12);
x_18 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg(x_1, x_6, x_17, x_14, x_15, x_5, x_13);
lean_dec(x_14);
lean_dec_ref(x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_array_get_size(x_1);
x_22 = lean_mk_empty_array_with_capacity(x_5);
x_23 = lean_nat_dec_lt(x_5, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec_ref(x_6);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_sharecommon_quick(x_19);
lean_dec(x_19);
x_26 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg(x_1, x_6, x_25, x_21, x_22, x_5, x_20);
lean_dec(x_21);
lean_dec_ref(x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Elab_shareCommonPreDefs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("share common exprs", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_shareCommonPreDefs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxSharing", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_shareCommonPreDefs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_shareCommonPreDefs___closed__1;
x_2 = l_Lean_Elab_fixLevelParams___closed__1;
x_3 = l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_shareCommonPreDefs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_shareCommonPreDefs___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_instInhabitedExpr;
x_7 = l_Lean_Elab_shareCommonPreDefs___closed__0;
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_shareCommonPreDefs___lam__0___boxed), 5, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_shareCommonPreDefs___closed__2;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Elab_shareCommonPreDefs___closed__3;
x_12 = lean_array_size(x_1);
x_13 = lean_box_usize(x_12);
x_14 = l_Lean_Elab_shareCommonPreDefs___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_shareCommonPreDefs___lam__1___boxed), 9, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_11);
lean_closure_set(x_15, 4, x_10);
lean_closure_set(x_15, 5, x_6);
x_16 = 1;
x_17 = l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_;
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___boxed), 9, 6);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_8);
lean_closure_set(x_19, 3, x_15);
lean_closure_set(x_19, 4, x_18);
lean_closure_set(x_19, 5, x_17);
x_20 = lean_box(0);
x_21 = l_Lean_profileitM___at___Lean_traceBlock_spec__0___redArg(x_7, x_5, x_19, x_20, x_2, x_3, x_4);
lean_dec(x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_shareCommonPreDefs_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_4);
x_18 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_shareCommonPreDefs_spec__1(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_shareCommonPreDefs___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_shareCommonPreDefs___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_shareCommonPreDefs___lam__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
return x_12;
}
}
lean_object* initialize_Init_ShareCommon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_NumApps(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LetToHave(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DefView(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_ShareCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NoncomputableAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_NumObjs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_NumApps(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractNestedProofs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ForEachExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LetToHave(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__7____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
l_Lean_Elab_initFn___closed__8____x40_Lean_Elab_PreDefinition_Basic___hyg_7_ = _init_l_Lean_Elab_initFn___closed__8____x40_Lean_Elab_PreDefinition_Basic___hyg_7_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__8____x40_Lean_Elab_PreDefinition_Basic___hyg_7_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Basic___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_cleanup_letToHave = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_cleanup_letToHave);
lean_dec_ref(res);
}l_Lean_Elab_instInhabitedPreDefinition___closed__0 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__0();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__0);
l_Lean_Elab_instInhabitedPreDefinition___closed__1 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__1);
l_Lean_Elab_instInhabitedPreDefinition___closed__2 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__2);
l_Lean_Elab_instInhabitedPreDefinition___closed__3 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__3();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__3);
l_Lean_Elab_instInhabitedPreDefinition___closed__4 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__4();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__4);
l_Lean_Elab_instInhabitedPreDefinition___closed__5 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__5();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__5);
l_Lean_Elab_instInhabitedPreDefinition___closed__6 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__6();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__6);
l_Lean_Elab_instInhabitedPreDefinition = _init_l_Lean_Elab_instInhabitedPreDefinition();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__0 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__0);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__3);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__4);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__5);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__6);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__7);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__8);
l_Lean_Elab_fixLevelParams___closed__0 = _init_l_Lean_Elab_fixLevelParams___closed__0();
lean_mark_persistent(l_Lean_Elab_fixLevelParams___closed__0);
l_Lean_Elab_fixLevelParams___closed__1 = _init_l_Lean_Elab_fixLevelParams___closed__1();
lean_mark_persistent(l_Lean_Elab_fixLevelParams___closed__1);
l_Lean_Elab_fixLevelParams___closed__2 = _init_l_Lean_Elab_fixLevelParams___closed__2();
lean_mark_persistent(l_Lean_Elab_fixLevelParams___closed__2);
l_Lean_Elab_fixLevelParams___closed__3 = _init_l_Lean_Elab_fixLevelParams___closed__3();
lean_mark_persistent(l_Lean_Elab_fixLevelParams___closed__3);
l_Lean_Elab_letToHaveValue___closed__0 = _init_l_Lean_Elab_letToHaveValue___closed__0();
lean_mark_persistent(l_Lean_Elab_letToHaveValue___closed__0);
l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_);
l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_ = _init_l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__2____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_);
l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_ = _init_l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__3____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_);
l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_ = _init_l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__4____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_);
l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_ = _init_l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__5____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_);
l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_ = _init_l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__6____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_Basic___hyg_1072_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_diagnostics_threshold_proofSize = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_diagnostics_threshold_proofSize);
lean_dec_ref(res);
}l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__0 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__0);
l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__1 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__1);
l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__2 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__2);
l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__3 = _init_l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_____private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag_spec__0___redArg___closed__3);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__0);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__2();
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__3);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__4);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__5);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__6);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__7);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__8);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_reportTheoremDiag___closed__9);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__0 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__0);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__2);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__3);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__4);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__5);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__6);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_checkMeta___lam__1___closed__7);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__0 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__0);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__2);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__3);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__4);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__5);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__6);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__7);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__8);
l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___closed__0 = _init_l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_eraseRecAppSyntaxExpr___lam__0___closed__0);
l_Lean_Elab_eraseRecAppSyntaxExpr___closed__0 = _init_l_Lean_Elab_eraseRecAppSyntaxExpr___closed__0();
lean_mark_persistent(l_Lean_Elab_eraseRecAppSyntaxExpr___closed__0);
l_Lean_Elab_addAndCompileUnsafe___boxed__const__1 = _init_l_Lean_Elab_addAndCompileUnsafe___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_addAndCompileUnsafe___boxed__const__1);
l_Lean_Elab_ensureNoRecFn___lam__0___closed__0 = _init_l_Lean_Elab_ensureNoRecFn___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_ensureNoRecFn___lam__0___closed__0);
l_Lean_Elab_ensureNoRecFn___lam__0___closed__1 = _init_l_Lean_Elab_ensureNoRecFn___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_ensureNoRecFn___lam__0___closed__1);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__0 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__0();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__0);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__1 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__1();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__1);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__2 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__2();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__2);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__3 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__3();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__3);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__4 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__4();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__4);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__5 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__5();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__5);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__6 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__6();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__6);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__7 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__7();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__7);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__8 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__8();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__8);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__9 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__9();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__9);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__10 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__10();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__10);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__11 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__11();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__11);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__12 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__12();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__12);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__13 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__13();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__13);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__14 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__14();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__14);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__15 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__15();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__15);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__16 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__16();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__16);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__17 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__17();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Elab_checkCodomainsLevel_spec__1_spec__1___redArg___lam__0___closed__17);
l_Lean_Elab_shareCommonPreDefs___closed__0 = _init_l_Lean_Elab_shareCommonPreDefs___closed__0();
lean_mark_persistent(l_Lean_Elab_shareCommonPreDefs___closed__0);
l_Lean_Elab_shareCommonPreDefs___closed__1 = _init_l_Lean_Elab_shareCommonPreDefs___closed__1();
lean_mark_persistent(l_Lean_Elab_shareCommonPreDefs___closed__1);
l_Lean_Elab_shareCommonPreDefs___closed__2 = _init_l_Lean_Elab_shareCommonPreDefs___closed__2();
lean_mark_persistent(l_Lean_Elab_shareCommonPreDefs___closed__2);
l_Lean_Elab_shareCommonPreDefs___closed__3 = _init_l_Lean_Elab_shareCommonPreDefs___closed__3();
lean_mark_persistent(l_Lean_Elab_shareCommonPreDefs___closed__3);
l_Lean_Elab_shareCommonPreDefs___boxed__const__1 = _init_l_Lean_Elab_shareCommonPreDefs___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_shareCommonPreDefs___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
