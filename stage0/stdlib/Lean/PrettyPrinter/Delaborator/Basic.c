// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Basic
// Imports: public import Lean.KeyedDeclsAttribute public import Lean.PrettyPrinter.Delaborator.TopDownAnalyze import Lean.Elab.InfoTree.Main import Lean.ExtraModUses public meta import Init.Data.ToString.Name
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* l_Lean_getPPProofs___boxed(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_getPPProofsThreshold___boxed(lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_Lean_Syntax_identComponents(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___redArg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getInfo_x3f(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_getPPMaxSteps___boxed(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_getPPDeepTerms___boxed(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
lean_object* l_Lean_getPPSafeShadowing___boxed(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_maxChildren;
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object*);
lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPDeepTermsThreshold___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_typeCoord;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_getPPProofsWithType___boxed(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Options_getInPattern(lean_object*);
lean_object* l_Lean_SubExpr_mkRoot(lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_getPPAll(lean_object*);
uint8_t l_Lean_getPPAnalyze(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPBeta(lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_erasePatternRefAnnotations(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_getPPInstantiateMVars(lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_pp_proofs;
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPMVarsLevels___boxed(lean_object*);
lean_object* l_Lean_MetavarContext_findLevelIndex_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote(lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
uint8_t l_Lean_getPPMVarsLevels(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "delabFailure"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 138, 190, 155, 112, 230, 57, 130)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFailureId;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_failure___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_orElse___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_orElse___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__0_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__0_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 158, 147, 61, 120, 131, 143, 40)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "builtin_delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 78, 157, 22, 7, 109, 94, 150)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 48, 28, 192, 106, 44, 69, 249)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Register a delaborator"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Delaborator"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 145, 52, 44, 66, 160, 163, 69)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "delabAttribute"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 105, 4, 51, 2, 59, 203, 237)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 513, .m_capacity = 513, .m_length = 512, .m_data = "Registers a delaborator.\n\n`@[delab k]` registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the\n`Lean.Expr` constructor `k`. Multiple delaborators for a single constructor are tried in turn until\nthe first success. If the term to be delaborated is an application of a constant `c`, elaborators\nfor `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\") to reduce\nspecial casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k` is tried first.\n"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(102) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(112) << 1) | 1)),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(40) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "attrApp_delab_"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 211, 248, 195, 71, 12, 182, 36)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__2_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__3_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "app_delab"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__4_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__5_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__6_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__7_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__7_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__8 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__8_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__3_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__5_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__8_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__9 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__9_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__9_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__10 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_PrettyPrinter_Delaborator_attrApp__delab__ = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__10_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ambiguous declaration `"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown declaration `"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mdata"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 175, 71, 113, 225, 183, 177, 137)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 199, 141, 14, 246, 212, 56, 18)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fvar"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 205, 14, 134, 100, 128, 23, 108)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mvar"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 4, 123, 224, 163, 191, 27, 224)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(219, 64, 188, 107, 37, 148, 192, 182)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8_value),LEAN_SCALAR_PTR_LITERAL(127, 151, 111, 115, 93, 99, 227, 194)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10_value),LEAN_SCALAR_PTR_LITERAL(74, 171, 42, 71, 5, 117, 56, 122)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12_value),LEAN_SCALAR_PTR_LITERAL(225, 230, 114, 173, 203, 123, 191, 0)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lit"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14_value),LEAN_SCALAR_PTR_LITERAL(45, 95, 104, 244, 171, 29, 119, 232)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16_value),LEAN_SCALAR_PTR_LITERAL(23, 181, 174, 77, 43, 228, 39, 210)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPSafeShadowing___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "Term omitted due to its depth (see option `pp.deepTerms`)."};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Proof omitted (see option `pp.proofs`)."};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 129, .m_capacity = 129, .m_length = 128, .m_data = "Term omitted due to reaching the maximum number of steps allowed for pretty printing this expression (see option `pp.maxSteps`)."};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPDeepTerms___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPDeepTermsThreshold___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPProofs___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPProofsThreshold___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "omission"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__1_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⋯"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "don't know how to delaborate `"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPMaxSteps___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__1_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__2_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__4_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__5 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__5_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__7_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__8;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__9 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__9_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__10 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__10_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__11 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value),LEAN_SCALAR_PTR_LITERAL(231, 152, 1, 212, 81, 225, 23, 202)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__12 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__12_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__11_value),LEAN_SCALAR_PTR_LITERAL(170, 131, 175, 90, 105, 49, 153, 209)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__14 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__14_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__15 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__16_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__17 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__17_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__18 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__19 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__15_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__19_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__20 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__20_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__13_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__20_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__21 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__21_value;
static const lean_ctor_object l_Lean_PrettyPrinter_Delaborator_delab___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__10_value),((lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__21_value)}};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__22 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__22_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__23 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__23_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_delab___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__24 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__24_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delab___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPAnalyzeTypeAscriptions___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__25 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__25_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delab___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPAnalysisNeedsType___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__26 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__26_value;
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delab___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPProofsWithType___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__27 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delab___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getPPMVarsLevels___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "app_unexpander"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 94, 177, 152, 198, 163, 81, 20)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Register an unexpander for applications of a given constant."};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Unexpander"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 37, 73, 100, 13, 145, 76, 255)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "appUnexpanderAttribute"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 126, 247, 124, 241, 28, 11, 244)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 177, 70, 181, 38, 19, 76, 236)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 620, .m_capacity = 620, .m_length = 619, .m_data = "Registers an unexpander for applications of a given constant.\n\n`@[app_unexpander c]` registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant\n`c`. The unexpander is passed the result of pre-pretty printing the application *without*\nimplicitly passed arguments. If `pp.explicit` is set to true or `pp.notation` is set to false,\nit will not be called at all.\n\nUnexpanders work as an alternative for delaborators (`@[app_delab]`) that can be used without\nspecial imports. This however also makes them much less capable since they can only transform\nsyntax and don't have access to the expression tree.\n"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(472) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(494) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(485) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(485) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_delabCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.PrettyPrinter.Delaborator.Basic"};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_delabCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PrettyPrinter.delabCore"};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_delabCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__2_value;
static lean_once_cell_t l_Lean_PrettyPrinter_delabCore___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__3;
static lean_once_cell_t l_Lean_PrettyPrinter_delabCore___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__4;
static lean_once_cell_t l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__5;
static const lean_string_object l_Lean_PrettyPrinter_delabCore___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "input"};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__6 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__6_value;
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
static const lean_ctor_object l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(104, 172, 119, 199, 92, 54, 86, 47)}};
static const lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__7 = (const lean_object*)&l_Lean_PrettyPrinter_delabCore___redArg___closed__7_value;
static lean_once_cell_t l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_delabCore___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_delab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delab___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_delab___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_delab___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 225, 73, 62, 228, 183, 164, 156)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 152, 45, 136, 43, 176, 59, 135)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 19, 214, 208, 28, 243, 5, 52)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 164, 190, 165, 103, 227, 105, 51)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(181, 183, 224, 255, 20, 2, 99, 61)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 0, 36, 13, 230, 137, 208, 68)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 99, 145, 72, 150, 13, 224, 205)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 207, 248, 169, 211, 175, 254, 249)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 170, 24, 58, 43, 56, 104, 232)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__7_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 123, 18, 109, 183, 228, 66, 1)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 193, 243, 64, 48, 31, 65, 146)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__9_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 168, 97, 241, 156, 42, 72, 1)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 126, 151, 159, 89, 238, 133, 226)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)(((size_t)(407216755) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(36, 100, 30, 138, 196, 203, 46, 101)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__20_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__20_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__20_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__21_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__20_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 229, 89, 61, 51, 113, 91, 110)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__21_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__21_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__22_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__22_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__22_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__23_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__21_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__22_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 172, 112, 17, 197, 244, 28, 218)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__23_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__23_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__23_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(222, 87, 20, 72, 25, 41, 179, 135)}};
static const lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_));
v___x_6_ = l_Lean_registerInternalExceptionId(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lam__0(lean_object* v___x_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_9_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lam__0___boxed(lean_object* v___x_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lam__0(v___x_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = l_Lean_instInhabitedMessageData_default;
v___x_28_ = lean_box(0);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___f_31_; 
v___x_30_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0, &l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__0);
v___f_31_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lam__0___boxed), 8, 1);
lean_closure_set(v___f_31_, 0, v___x_30_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object* v_00_u03b1_32_){
_start:
{
lean_object* v___f_33_; 
v___f_33_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1, &l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___redArg(lean_object* v_d_u2081_34_, lean_object* v_d_u2082_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
v___x_43_ = lean_apply_7(v_d_u2081_34_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
if (lean_obj_tag(v___x_43_) == 0)
{
lean_dec_ref(v_d_u2082_35_);
return v___x_43_;
}
else
{
lean_object* v_a_44_; lean_object* v___x_45_; uint8_t v___y_47_; uint8_t v___x_52_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_44_);
v___x_45_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_52_ = l_Lean_Exception_isInterrupt(v_a_44_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
lean_inc(v_a_44_);
v___x_53_ = l_Lean_Exception_isRuntime(v_a_44_);
v___y_47_ = v___x_53_;
goto v___jp_46_;
}
else
{
v___y_47_ = v___x_52_;
goto v___jp_46_;
}
v___jp_46_:
{
if (v___y_47_ == 0)
{
if (lean_obj_tag(v_a_44_) == 0)
{
lean_dec_ref_known(v_a_44_, 2);
lean_dec_ref(v_d_u2082_35_);
return v___x_43_;
}
else
{
lean_object* v_id_48_; uint8_t v___x_49_; 
v_id_48_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_id_48_);
lean_dec_ref_known(v_a_44_, 2);
v___x_49_ = l_Lean_instBEqInternalExceptionId_beq(v___x_45_, v_id_48_);
lean_dec(v_id_48_);
if (v___x_49_ == 0)
{
lean_dec_ref(v_d_u2082_35_);
return v___x_43_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec_ref_known(v___x_43_, 1);
v___x_50_ = lean_box(0);
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
v___x_51_ = lean_apply_8(v_d_u2082_35_, v___x_50_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_51_;
}
}
}
else
{
lean_dec(v_a_44_);
lean_dec_ref(v_d_u2082_35_);
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___redArg___boxed(lean_object* v_d_u2081_54_, lean_object* v_d_u2082_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_PrettyPrinter_Delaborator_orElse___redArg(v_d_u2081_54_, v_d_u2082_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object* v_00_u03b1_64_, lean_object* v_d_u2081_65_, lean_object* v_d_u2082_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
lean_inc(v_a_72_);
lean_inc_ref(v_a_71_);
lean_inc(v_a_70_);
lean_inc_ref(v_a_69_);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
v___x_74_ = lean_apply_7(v_d_u2081_65_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, lean_box(0));
if (lean_obj_tag(v___x_74_) == 0)
{
lean_dec_ref(v_d_u2082_66_);
return v___x_74_;
}
else
{
lean_object* v_a_75_; lean_object* v___x_76_; uint8_t v___y_78_; uint8_t v___x_83_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
v___x_76_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_83_ = l_Lean_Exception_isInterrupt(v_a_75_);
if (v___x_83_ == 0)
{
uint8_t v___x_84_; 
lean_inc(v_a_75_);
v___x_84_ = l_Lean_Exception_isRuntime(v_a_75_);
v___y_78_ = v___x_84_;
goto v___jp_77_;
}
else
{
v___y_78_ = v___x_83_;
goto v___jp_77_;
}
v___jp_77_:
{
if (v___y_78_ == 0)
{
if (lean_obj_tag(v_a_75_) == 0)
{
lean_dec_ref_known(v_a_75_, 2);
lean_dec_ref(v_d_u2082_66_);
return v___x_74_;
}
else
{
lean_object* v_id_79_; uint8_t v___x_80_; 
v_id_79_ = lean_ctor_get(v_a_75_, 0);
lean_inc(v_id_79_);
lean_dec_ref_known(v_a_75_, 2);
v___x_80_ = l_Lean_instBEqInternalExceptionId_beq(v___x_76_, v_id_79_);
lean_dec(v_id_79_);
if (v___x_80_ == 0)
{
lean_dec_ref(v_d_u2082_66_);
return v___x_74_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref_known(v___x_74_, 1);
v___x_81_ = lean_box(0);
lean_inc(v_a_72_);
lean_inc_ref(v_a_71_);
lean_inc(v_a_70_);
lean_inc_ref(v_a_69_);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
v___x_82_ = lean_apply_8(v_d_u2082_66_, v___x_81_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, lean_box(0));
return v___x_82_;
}
}
}
else
{
lean_dec(v_a_75_);
lean_dec_ref(v_d_u2082_66_);
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___boxed(lean_object* v_00_u03b1_85_, lean_object* v_d_u2081_86_, lean_object* v_d_u2082_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_PrettyPrinter_Delaborator_orElse(v_00_u03b1_85_, v_d_u2081_86_, v_d_u2082_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_95_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg(){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0, &l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_failure___redArg___closed__0);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg___boxed(lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object* v_00_u03b1_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object* v_00_u03b1_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_PrettyPrinter_Delaborator_failure(v_00_u03b1_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_instMonadEIO(lean_box(0));
return v___x_122_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__0);
v___x_124_ = l_StateRefT_x27_instMonad___redArg(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM(void){
_start:
{
lean_object* v___x_131_; lean_object* v_toApplicative_132_; lean_object* v_toFunctor_133_; lean_object* v_toSeq_134_; lean_object* v_toSeqLeft_135_; lean_object* v_toSeqRight_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_toApplicative_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_199_; 
v___x_131_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1, &l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1);
v_toApplicative_132_ = lean_ctor_get(v___x_131_, 0);
v_toFunctor_133_ = lean_ctor_get(v_toApplicative_132_, 0);
v_toSeq_134_ = lean_ctor_get(v_toApplicative_132_, 2);
v_toSeqLeft_135_ = lean_ctor_get(v_toApplicative_132_, 3);
v_toSeqRight_136_ = lean_ctor_get(v_toApplicative_132_, 4);
v___f_137_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2));
v___f_138_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3));
lean_inc_ref_n(v_toFunctor_133_, 2);
v___f_139_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_139_, 0, v_toFunctor_133_);
v___f_140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_140_, 0, v_toFunctor_133_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___f_139_);
lean_ctor_set(v___x_141_, 1, v___f_140_);
lean_inc(v_toSeqRight_136_);
v___f_142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_142_, 0, v_toSeqRight_136_);
lean_inc(v_toSeqLeft_135_);
v___f_143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_143_, 0, v_toSeqLeft_135_);
lean_inc(v_toSeq_134_);
v___f_144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_144_, 0, v_toSeq_134_);
v___x_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_145_, 0, v___x_141_);
lean_ctor_set(v___x_145_, 1, v___f_137_);
lean_ctor_set(v___x_145_, 2, v___f_144_);
lean_ctor_set(v___x_145_, 3, v___f_143_);
lean_ctor_set(v___x_145_, 4, v___f_142_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___f_138_);
v___x_147_ = l_StateRefT_x27_instMonad___redArg(v___x_146_);
v_toApplicative_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v___x_147_, 1);
lean_dec(v_unused_200_);
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_199_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_toApplicative_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_199_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v_toFunctor_152_; lean_object* v_toSeq_153_; lean_object* v_toSeqLeft_154_; lean_object* v_toSeqRight_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_197_; 
v_toFunctor_152_ = lean_ctor_get(v_toApplicative_148_, 0);
v_toSeq_153_ = lean_ctor_get(v_toApplicative_148_, 2);
v_toSeqLeft_154_ = lean_ctor_get(v_toApplicative_148_, 3);
v_toSeqRight_155_ = lean_ctor_get(v_toApplicative_148_, 4);
v_isSharedCheck_197_ = !lean_is_exclusive(v_toApplicative_148_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v_toApplicative_148_, 1);
lean_dec(v_unused_198_);
v___x_157_ = v_toApplicative_148_;
v_isShared_158_ = v_isSharedCheck_197_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_toSeqRight_155_);
lean_inc(v_toSeqLeft_154_);
lean_inc(v_toSeq_153_);
lean_inc(v_toFunctor_152_);
lean_dec(v_toApplicative_148_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_197_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___x_163_; lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___x_168_; 
v___f_159_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4));
v___f_160_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5));
lean_inc_ref(v_toFunctor_152_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_161_, 0, v_toFunctor_152_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_162_, 0, v_toFunctor_152_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___f_161_);
lean_ctor_set(v___x_163_, 1, v___f_162_);
v___f_164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_164_, 0, v_toSeqRight_155_);
v___f_165_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_165_, 0, v_toSeqLeft_154_);
v___f_166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_166_, 0, v_toSeq_153_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 4, v___f_164_);
lean_ctor_set(v___x_157_, 3, v___f_165_);
lean_ctor_set(v___x_157_, 2, v___f_166_);
lean_ctor_set(v___x_157_, 1, v___f_159_);
lean_ctor_set(v___x_157_, 0, v___x_163_);
v___x_168_ = v___x_157_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___f_159_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v___f_166_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v___f_165_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v___f_164_);
v___x_168_ = v_reuseFailAlloc_196_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_170_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___f_160_);
lean_ctor_set(v___x_150_, 0, v___x_168_);
v___x_170_ = v___x_150_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v___f_160_);
v___x_170_ = v_reuseFailAlloc_195_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v_toApplicative_172_; lean_object* v_toFunctor_173_; lean_object* v_toSeq_174_; lean_object* v_toSeqLeft_175_; lean_object* v_toSeqRight_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_193_; 
v___x_171_ = l_StateRefT_x27_instMonad___redArg(v___x_170_);
v_toApplicative_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc_ref(v_toApplicative_172_);
v_toFunctor_173_ = lean_ctor_get(v_toApplicative_172_, 0);
v_toSeq_174_ = lean_ctor_get(v_toApplicative_172_, 2);
v_toSeqLeft_175_ = lean_ctor_get(v_toApplicative_172_, 3);
v_toSeqRight_176_ = lean_ctor_get(v_toApplicative_172_, 4);
v_isSharedCheck_193_ = !lean_is_exclusive(v_toApplicative_172_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v_toApplicative_172_, 1);
lean_dec(v_unused_194_);
v___x_178_ = v_toApplicative_172_;
v_isShared_179_ = v_isSharedCheck_193_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_toSeqRight_176_);
lean_inc(v_toSeqLeft_175_);
lean_inc(v_toSeq_174_);
lean_inc(v_toFunctor_173_);
lean_dec(v_toApplicative_172_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_193_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_180_, 0, v_toSeqRight_176_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_181_, 0, v_toSeqLeft_175_);
v___f_182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_182_, 0, v_toSeq_174_);
lean_inc_ref(v_toFunctor_173_);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_183_, 0, v_toFunctor_173_);
v___f_184_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_184_, 0, v_toFunctor_173_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___f_183_);
lean_ctor_set(v___x_185_, 1, v___f_184_);
v___x_186_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_186_, 0, lean_box(0));
lean_closure_set(v___x_186_, 1, lean_box(0));
lean_closure_set(v___x_186_, 2, v___x_171_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___f_180_);
lean_ctor_set(v___x_178_, 3, v___f_181_);
lean_ctor_set(v___x_178_, 2, v___f_182_);
lean_ctor_set(v___x_178_, 1, v___x_186_);
lean_ctor_set(v___x_178_, 0, v___x_185_);
v___x_188_ = v___x_178_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v___f_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v___f_181_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v___f_180_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6));
v___x_190_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__7));
v___x_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_188_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_190_);
return v___x_191_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object* v_00_u03b1_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__0));
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_subExpr_211_; lean_object* v___x_212_; 
v_subExpr_211_ = lean_ctor_get(v___y_204_, 3);
lean_inc_ref(v_subExpr_211_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v_subExpr_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0___boxed(lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lam__0(v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(lean_object* v_00_u03b1_223_, lean_object* v_f_224_, lean_object* v_x_225_, lean_object* v_ctx_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_optionsPerPos_233_; lean_object* v_currNamespace_234_; lean_object* v_openDecls_235_; uint8_t v_inPattern_236_; lean_object* v_subExpr_237_; lean_object* v_depth_238_; lean_object* v_lctxInitIndices_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_248_; 
v_optionsPerPos_233_ = lean_ctor_get(v_ctx_226_, 0);
v_currNamespace_234_ = lean_ctor_get(v_ctx_226_, 1);
v_openDecls_235_ = lean_ctor_get(v_ctx_226_, 2);
v_inPattern_236_ = lean_ctor_get_uint8(v_ctx_226_, sizeof(void*)*6);
v_subExpr_237_ = lean_ctor_get(v_ctx_226_, 3);
v_depth_238_ = lean_ctor_get(v_ctx_226_, 4);
v_lctxInitIndices_239_ = lean_ctor_get(v_ctx_226_, 5);
v_isSharedCheck_248_ = !lean_is_exclusive(v_ctx_226_);
if (v_isSharedCheck_248_ == 0)
{
v___x_241_ = v_ctx_226_;
v_isShared_242_ = v_isSharedCheck_248_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_lctxInitIndices_239_);
lean_inc(v_depth_238_);
lean_inc(v_subExpr_237_);
lean_inc(v_openDecls_235_);
lean_inc(v_currNamespace_234_);
lean_inc(v_optionsPerPos_233_);
lean_dec(v_ctx_226_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_248_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_apply_1(v_f_224_, v_subExpr_237_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 3, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_optionsPerPos_233_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_currNamespace_234_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_openDecls_235_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_247_, 4, v_depth_238_);
lean_ctor_set(v_reuseFailAlloc_247_, 5, v_lctxInitIndices_239_);
lean_ctor_set_uint8(v_reuseFailAlloc_247_, sizeof(void*)*6, v_inPattern_236_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; 
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
lean_inc(v___y_227_);
v___x_246_ = lean_apply_7(v_x_225_, v___x_245_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, lean_box(0));
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0___boxed(lean_object* v_00_u03b1_249_, lean_object* v_f_250_, lean_object* v_x_251_, lean_object* v_ctx_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___lam__0(v_00_u03b1_249_, v_f_250_, v_x_251_, v_ctx_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v_holeIter_270_; lean_object* v___x_271_; 
v___x_269_ = lean_st_ref_get(v___y_263_);
v_holeIter_270_ = lean_ctor_get(v___x_269_, 2);
lean_inc_ref(v_holeIter_270_);
lean_dec(v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v_holeIter_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0___boxed(lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__0(v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(lean_object* v_iter_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_steps_289_; lean_object* v_infos_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_300_; 
v___x_288_ = lean_st_ref_take(v___y_282_);
v_steps_289_ = lean_ctor_get(v___x_288_, 0);
v_infos_290_ = lean_ctor_get(v___x_288_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_288_, 2);
lean_dec(v_unused_301_);
v___x_292_ = v___x_288_;
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_infos_290_);
lean_inc(v_steps_289_);
lean_dec(v___x_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_300_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 2, v_iter_280_);
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_steps_289_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_infos_290_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_iter_280_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_st_ref_put(v___y_282_, v___x_295_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1___boxed(lean_object* v_iter_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__1(v_iter_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(lean_object* v_00_u03b1_311_, lean_object* v_f_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; lean_object* v_steps_321_; lean_object* v_infos_322_; lean_object* v_holeIter_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_335_; 
v___x_320_ = lean_st_ref_take(v___y_314_);
v_steps_321_ = lean_ctor_get(v___x_320_, 0);
v_infos_322_ = lean_ctor_get(v___x_320_, 1);
v_holeIter_323_ = lean_ctor_get(v___x_320_, 2);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_335_ == 0)
{
v___x_325_ = v___x_320_;
v_isShared_326_ = v_isSharedCheck_335_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_holeIter_323_);
lean_inc(v_infos_322_);
lean_inc(v_steps_321_);
lean_dec(v___x_320_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_335_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_331_; 
v___x_327_ = lean_apply_1(v_f_312_, v_holeIter_323_);
v_fst_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_fst_328_);
v_snd_329_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_329_);
lean_dec_ref(v___x_327_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 2, v_snd_329_);
v___x_331_ = v___x_325_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_steps_321_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_infos_322_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_snd_329_);
v___x_331_ = v_reuseFailAlloc_334_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_st_ref_put(v___y_314_, v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v_fst_328_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2___boxed(lean_object* v_00_u03b1_336_, lean_object* v_f_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lam__2(v_00_u03b1_336_, v_f_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t v_builtin_354_, lean_object* v_declName_355_, lean_object* v_key_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_builtin_362_, lean_object* v_declName_363_, lean_object* v_key_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
uint8_t v_builtin_boxed_368_; lean_object* v_res_369_; 
v_builtin_boxed_368_ = lean_unbox(v_builtin_362_);
v_res_369_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(v_builtin_boxed_368_, v_declName_363_, v_key_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v_key_364_);
lean_dec(v_declName_363_);
return v_res_369_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__0);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
lean_ctor_set(v___x_375_, 3, v___x_374_);
lean_ctor_set(v___x_375_, 4, v___x_373_);
lean_ctor_set(v___x_375_, 5, v___x_373_);
lean_ctor_set(v___x_375_, 6, v___x_373_);
lean_ctor_set(v___x_375_, 7, v___x_373_);
lean_ctor_set(v___x_375_, 8, v___x_373_);
lean_ctor_set(v___x_375_, 9, v___x_373_);
lean_ctor_set(v___x_375_, 10, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_unsigned_to_nat(32u);
v___x_377_ = lean_mk_empty_array_with_capacity(v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4(void){
_start:
{
size_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_379_ = ((size_t)5ULL);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_unsigned_to_nat(32u);
v___x_382_ = lean_mk_empty_array_with_capacity(v___x_381_);
v___x_383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__3);
v___x_384_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_380_);
lean_ctor_set(v___x_384_, 3, v___x_380_);
lean_ctor_set_usize(v___x_384_, 4, v___x_379_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_box(1);
v___x_386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__1);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_385_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__6));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__8));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__10));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__12));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__14));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__16));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__18));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(lean_object* v_msg_410_, lean_object* v_declHint_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_env_415_; uint8_t v___x_416_; 
v___x_414_ = lean_st_ref_get(v___y_412_);
v_env_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_env_415_);
lean_dec(v___x_414_);
v___x_416_ = l_Lean_Name_isAnonymous(v_declHint_411_);
if (v___x_416_ == 0)
{
uint8_t v_isExporting_417_; 
v_isExporting_417_ = lean_ctor_get_uint8(v_env_415_, sizeof(void*)*8);
if (v_isExporting_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec_ref(v_env_415_);
lean_dec(v_declHint_411_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v_msg_410_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; uint8_t v___x_420_; 
lean_inc_ref(v_env_415_);
v___x_419_ = l_Lean_Environment_setExporting(v_env_415_, v___x_416_);
lean_inc(v_declHint_411_);
lean_inc_ref(v___x_419_);
v___x_420_ = l_Lean_Environment_contains(v___x_419_, v_declHint_411_, v_isExporting_417_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec_ref(v___x_419_);
lean_dec_ref(v_env_415_);
lean_dec(v_declHint_411_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v_msg_410_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_c_427_; lean_object* v___x_428_; 
v___x_422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
v___x_424_ = l_Lean_Options_empty;
v___x_425_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_425_, 0, v___x_419_);
lean_ctor_set(v___x_425_, 1, v___x_422_);
lean_ctor_set(v___x_425_, 2, v___x_423_);
lean_ctor_set(v___x_425_, 3, v___x_424_);
lean_inc(v_declHint_411_);
v___x_426_ = l_Lean_MessageData_ofConstName(v_declHint_411_, v___x_416_);
v_c_427_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_427_, 0, v___x_425_);
lean_ctor_set(v_c_427_, 1, v___x_426_);
v___x_428_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_415_, v_declHint_411_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v_env_415_);
lean_dec(v_declHint_411_);
v___x_429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_c_427_);
v___x_431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__9);
v___x_432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_MessageData_note(v___x_432_);
v___x_434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_434_, 0, v_msg_410_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
else
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_471_; 
v_val_436_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_471_ == 0)
{
v___x_438_ = v___x_428_;
v_isShared_439_ = v_isSharedCheck_471_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v___x_428_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_471_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_mod_443_; uint8_t v___x_444_; 
v___x_440_ = lean_box(0);
v___x_441_ = l_Lean_Environment_header(v_env_415_);
lean_dec_ref(v_env_415_);
v___x_442_ = l_Lean_EnvironmentHeader_moduleNames(v___x_441_);
v_mod_443_ = lean_array_get(v___x_440_, v___x_442_, v_val_436_);
lean_dec(v_val_436_);
lean_dec_ref(v___x_442_);
v___x_444_ = l_Lean_isPrivateName(v_declHint_411_);
lean_dec(v_declHint_411_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_445_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__11);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_c_427_);
v___x_447_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__13);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_MessageData_ofName(v_mod_443_);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__15);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = l_Lean_MessageData_note(v___x_452_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v_msg_410_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 0);
lean_ctor_set(v___x_438_, 0, v___x_454_);
v___x_456_ = v___x_438_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_458_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__7);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_c_427_);
v___x_460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__17);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_MessageData_ofName(v_mod_443_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__19);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_MessageData_note(v___x_465_);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v_msg_410_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 0);
lean_ctor_set(v___x_438_, 0, v___x_467_);
v___x_469_ = v___x_438_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_472_; 
lean_dec_ref(v_env_415_);
lean_dec(v_declHint_411_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v_msg_410_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___boxed(lean_object* v_msg_473_, lean_object* v_declHint_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_473_, v_declHint_474_, v___y_475_);
lean_dec(v___y_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(lean_object* v_msg_478_, lean_object* v_declHint_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_493_; 
v___x_483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_478_, v_declHint_479_, v___y_481_);
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_493_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = l_Lean_unknownIdentifierMessageTag;
v___x_489_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_a_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_489_);
v___x_491_ = v___x_486_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msg_494_, lean_object* v_declHint_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_494_, v_declHint_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_msgData_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v_toCold_505_; lean_object* v_env_506_; lean_object* v_options_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_504_ = lean_st_ref_get(v___y_502_);
v_toCold_505_ = lean_ctor_get(v___y_501_, 0);
v_env_506_ = lean_ctor_get(v___x_504_, 0);
lean_inc_ref(v_env_506_);
lean_dec(v___x_504_);
v_options_507_ = lean_ctor_get(v_toCold_505_, 2);
v___x_508_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__2);
v___x_509_ = lean_unsigned_to_nat(32u);
v___x_510_ = lean_mk_empty_array_with_capacity(v___x_509_);
lean_dec_ref(v___x_510_);
v___x_511_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__5);
lean_inc_ref(v_options_507_);
v___x_512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_512_, 0, v_env_506_);
lean_ctor_set(v___x_512_, 1, v___x_508_);
lean_ctor_set(v___x_512_, 2, v___x_511_);
lean_ctor_set(v___x_512_, 3, v_options_507_);
v___x_513_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v_msgData_500_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_msgData_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msgData_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_ref_524_; lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
v_ref_524_ = lean_ctor_get(v___y_521_, 2);
v___x_525_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_520_, v___y_521_, v___y_522_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
lean_inc(v_ref_524_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_ref_524_);
lean_ctor_set(v___x_530_, 1, v_a_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set_tag(v___x_528_, 1);
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg___boxed(lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_ref_540_, lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_toCold_545_; lean_object* v_currRecDepth_546_; lean_object* v_ref_547_; uint8_t v_diag_548_; uint8_t v_suppressElabErrors_549_; lean_object* v_ref_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_toCold_545_ = lean_ctor_get(v___y_542_, 0);
v_currRecDepth_546_ = lean_ctor_get(v___y_542_, 1);
v_ref_547_ = lean_ctor_get(v___y_542_, 2);
v_diag_548_ = lean_ctor_get_uint8(v___y_542_, sizeof(void*)*3);
v_suppressElabErrors_549_ = lean_ctor_get_uint8(v___y_542_, sizeof(void*)*3 + 1);
v_ref_550_ = l_Lean_replaceRef(v_ref_540_, v_ref_547_);
lean_inc(v_currRecDepth_546_);
lean_inc_ref(v_toCold_545_);
v___x_551_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_551_, 0, v_toCold_545_);
lean_ctor_set(v___x_551_, 1, v_currRecDepth_546_);
lean_ctor_set(v___x_551_, 2, v_ref_550_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*3, v_diag_548_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*3 + 1, v_suppressElabErrors_549_);
v___x_552_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_541_, v___x_551_, v___y_543_);
lean_dec_ref_known(v___x_551_, 3);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_ref_553_, lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_553_, v_msg_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v_ref_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(lean_object* v_ref_559_, lean_object* v_msg_560_, lean_object* v_declHint_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; lean_object* v_a_566_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19(v_msg_560_, v_declHint_561_, v___y_562_, v___y_563_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref(v___x_565_);
v___x_567_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_559_, v_a_566_, v___y_562_, v___y_563_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_ref_568_, lean_object* v_msg_569_, lean_object* v_declHint_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_568_, v_msg_569_, v_declHint_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v_ref_568_);
return v_res_574_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__0));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(lean_object* v_ref_581_, lean_object* v_constName_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_586_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__1);
v___x_587_ = 0;
lean_inc(v_constName_582_);
v___x_588_ = l_Lean_MessageData_ofConstName(v_constName_582_, v___x_587_);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_586_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_581_, v___x_591_, v_constName_582_, v___y_583_, v___y_584_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_ref_593_, lean_object* v_constName_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_593_, v_constName_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v_ref_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(lean_object* v_constName_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_ref_603_; lean_object* v___x_604_; 
v_ref_603_ = lean_ctor_get(v___y_600_, 2);
v___x_604_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_603_, v_constName_599_, v___y_600_, v___y_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_constName_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(lean_object* v_constName_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; lean_object* v_env_615_; uint8_t v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_st_ref_get(v___y_612_);
v_env_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_env_615_);
lean_dec(v___x_614_);
v___x_616_ = 0;
lean_inc(v_constName_610_);
v___x_617_ = l_Lean_Environment_findConstVal_x3f(v_env_615_, v_constName_610_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_610_, v___y_611_, v___y_612_);
return v___x_618_;
}
else
{
lean_object* v_val_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_constName_610_);
v_val_619_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_617_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_val_619_);
lean_dec(v___x_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 0);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_val_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11___boxed(lean_object* v_constName_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
if (lean_obj_tag(v_a_632_) == 0)
{
lean_object* v___x_634_; 
v___x_634_ = l_List_reverse___redArg(v_a_633_);
return v___x_634_;
}
else
{
lean_object* v_head_635_; lean_object* v_tail_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
v_head_635_ = lean_ctor_get(v_a_632_, 0);
v_tail_636_ = lean_ctor_get(v_a_632_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_a_632_);
if (v_isSharedCheck_645_ == 0)
{
v___x_638_ = v_a_632_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_tail_636_);
lean_inc(v_head_635_);
lean_dec(v_a_632_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = l_Lean_mkLevelParam(v_head_635_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v_a_633_);
lean_ctor_set(v___x_638_, 0, v___x_640_);
v___x_642_ = v___x_638_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_a_633_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
v_a_632_ = v_tail_636_;
v_a_633_ = v___x_642_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(lean_object* v_constName_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___x_650_; 
lean_inc(v_constName_646_);
v___x_650_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11(v_constName_646_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_662_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_662_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_662_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_levelParams_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v_levelParams_655_ = lean_ctor_get(v_a_651_, 1);
lean_inc(v_levelParams_655_);
lean_dec(v_a_651_);
v___x_656_ = lean_box(0);
v___x_657_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__12(v_levelParams_655_, v___x_656_);
v___x_658_ = l_Lean_mkConst(v_constName_646_, v___x_657_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_658_);
v___x_660_ = v___x_653_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec(v_constName_646_);
v_a_663_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_650_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_650_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6___boxed(lean_object* v_constName_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_constName_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_t_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v_infoState_680_; uint8_t v_enabled_681_; 
v___x_679_ = lean_st_ref_get(v___y_677_);
v_infoState_680_ = lean_ctor_get(v___x_679_, 7);
lean_inc_ref(v_infoState_680_);
lean_dec(v___x_679_);
v_enabled_681_ = lean_ctor_get_uint8(v_infoState_680_, sizeof(void*)*3);
lean_dec_ref(v_infoState_680_);
if (v_enabled_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref(v_t_676_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v_infoState_685_; lean_object* v_env_686_; lean_object* v_nextMacroScope_687_; lean_object* v_ngen_688_; lean_object* v_auxDeclNGen_689_; lean_object* v_traceState_690_; lean_object* v_cache_691_; lean_object* v_messages_692_; lean_object* v_snapshotTasks_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_715_; 
v___x_684_ = lean_st_ref_take(v___y_677_);
v_infoState_685_ = lean_ctor_get(v___x_684_, 7);
v_env_686_ = lean_ctor_get(v___x_684_, 0);
v_nextMacroScope_687_ = lean_ctor_get(v___x_684_, 1);
v_ngen_688_ = lean_ctor_get(v___x_684_, 2);
v_auxDeclNGen_689_ = lean_ctor_get(v___x_684_, 3);
v_traceState_690_ = lean_ctor_get(v___x_684_, 4);
v_cache_691_ = lean_ctor_get(v___x_684_, 5);
v_messages_692_ = lean_ctor_get(v___x_684_, 6);
v_snapshotTasks_693_ = lean_ctor_get(v___x_684_, 8);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_715_ == 0)
{
v___x_695_ = v___x_684_;
v_isShared_696_ = v_isSharedCheck_715_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snapshotTasks_693_);
lean_inc(v_infoState_685_);
lean_inc(v_messages_692_);
lean_inc(v_cache_691_);
lean_inc(v_traceState_690_);
lean_inc(v_auxDeclNGen_689_);
lean_inc(v_ngen_688_);
lean_inc(v_nextMacroScope_687_);
lean_inc(v_env_686_);
lean_dec(v___x_684_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_715_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
uint8_t v_enabled_697_; lean_object* v_assignment_698_; lean_object* v_lazyAssignment_699_; lean_object* v_trees_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_714_; 
v_enabled_697_ = lean_ctor_get_uint8(v_infoState_685_, sizeof(void*)*3);
v_assignment_698_ = lean_ctor_get(v_infoState_685_, 0);
v_lazyAssignment_699_ = lean_ctor_get(v_infoState_685_, 1);
v_trees_700_ = lean_ctor_get(v_infoState_685_, 2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_infoState_685_);
if (v_isSharedCheck_714_ == 0)
{
v___x_702_ = v_infoState_685_;
v_isShared_703_ = v_isSharedCheck_714_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_trees_700_);
lean_inc(v_lazyAssignment_699_);
lean_inc(v_assignment_698_);
lean_dec(v_infoState_685_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_714_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = l_Lean_PersistentArray_push___redArg(v_trees_700_, v_t_676_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 2, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_assignment_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_lazyAssignment_699_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v___x_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*3, v_enabled_697_);
v___x_706_ = v_reuseFailAlloc_713_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 7, v___x_706_);
v___x_708_ = v___x_695_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_env_686_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_nextMacroScope_687_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_ngen_688_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_auxDeclNGen_689_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_traceState_690_);
lean_ctor_set(v_reuseFailAlloc_712_, 5, v_cache_691_);
lean_ctor_set(v_reuseFailAlloc_712_, 6, v_messages_692_);
lean_ctor_set(v_reuseFailAlloc_712_, 7, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_712_, 8, v_snapshotTasks_693_);
v___x_708_ = v_reuseFailAlloc_712_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_st_ref_put(v___y_677_, v___x_708_);
v___x_710_ = lean_box(0);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_t_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_716_, v___y_717_);
lean_dec(v___y_717_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_unsigned_to_nat(32u);
v___x_721_ = lean_mk_empty_array_with_capacity(v___x_720_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
size_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_723_ = ((size_t)5ULL);
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_unsigned_to_nat(32u);
v___x_726_ = lean_mk_empty_array_with_capacity(v___x_725_);
v___x_727_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_728_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_724_);
lean_ctor_set(v___x_728_, 3, v___x_724_);
lean_ctor_set_usize(v___x_728_, 4, v___x_723_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_t_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; lean_object* v_infoState_734_; uint8_t v_enabled_735_; 
v___x_733_ = lean_st_ref_get(v___y_731_);
v_infoState_734_ = lean_ctor_get(v___x_733_, 7);
lean_inc_ref(v_infoState_734_);
lean_dec(v___x_733_);
v_enabled_735_ = lean_ctor_get_uint8(v_infoState_734_, sizeof(void*)*3);
lean_dec_ref(v_infoState_734_);
if (v_enabled_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v_t_729_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v_t_729_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_739_, v___y_731_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_t_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v_t_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(lean_object* v_stx_746_, lean_object* v_n_747_, lean_object* v_expectedType_x3f_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6(v_n_747_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = lean_box(0);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_stx_746_);
v___x_756_ = l_Lean_LocalContext_empty;
v___x_757_ = 0;
v___x_758_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_758_, 0, v___x_755_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
lean_ctor_set(v___x_758_, 2, v_expectedType_x3f_748_);
lean_ctor_set(v___x_758_, 3, v_a_753_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*4, v___x_757_);
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*4 + 1, v___x_757_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___x_760_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_759_, v___y_749_, v___y_750_);
return v___x_760_;
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_expectedType_x3f_748_);
lean_dec(v_stx_746_);
v_a_761_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_752_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_752_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2___boxed(lean_object* v_stx_769_, lean_object* v_n_770_, lean_object* v_expectedType_x3f_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v_stx_769_, v_n_770_, v_expectedType_x3f_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(lean_object* v_info_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_780_, 0, v_info_776_);
v___x_781_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0(v___x_780_, v___y_777_, v___y_778_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0___boxed(lean_object* v_info_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v_info_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_box(0);
return v___x_789_;
}
else
{
lean_object* v_key_790_; lean_object* v_value_791_; lean_object* v_tail_792_; uint8_t v___x_793_; 
v_key_790_ = lean_ctor_get(v_x_788_, 0);
v_value_791_ = lean_ctor_get(v_x_788_, 1);
v_tail_792_ = lean_ctor_get(v_x_788_, 2);
v___x_793_ = lean_name_eq(v_key_790_, v_a_787_);
if (v___x_793_ == 0)
{
v_x_788_ = v_tail_792_;
goto _start;
}
else
{
lean_object* v___x_795_; 
lean_inc(v_value_791_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v_value_791_);
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_796_, v_x_797_);
lean_dec(v_x_797_);
lean_dec(v_a_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_m_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_buckets_801_; lean_object* v___x_802_; uint64_t v___y_804_; 
v_buckets_801_ = lean_ctor_get(v_m_799_, 1);
v___x_802_ = lean_array_get_size(v_buckets_801_);
if (lean_obj_tag(v_a_800_) == 0)
{
uint64_t v___x_818_; 
v___x_818_ = 1723ULL;
v___y_804_ = v___x_818_;
goto v___jp_803_;
}
else
{
uint64_t v_hash_819_; 
v_hash_819_ = lean_ctor_get_uint64(v_a_800_, sizeof(void*)*2);
v___y_804_ = v_hash_819_;
goto v___jp_803_;
}
v___jp_803_:
{
uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v_fold_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_805_ = 32ULL;
v___x_806_ = lean_uint64_shift_right(v___y_804_, v___x_805_);
v_fold_807_ = lean_uint64_xor(v___y_804_, v___x_806_);
v___x_808_ = 16ULL;
v___x_809_ = lean_uint64_shift_right(v_fold_807_, v___x_808_);
v___x_810_ = lean_uint64_xor(v_fold_807_, v___x_809_);
v___x_811_ = lean_uint64_to_usize(v___x_810_);
v___x_812_ = lean_usize_of_nat(v___x_802_);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_sub(v___x_812_, v___x_813_);
v___x_815_ = lean_usize_land(v___x_811_, v___x_814_);
v___x_816_ = lean_array_uget_borrowed(v_buckets_801_, v___x_815_);
v___x_817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_800_, v___x_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_m_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_m_820_);
return v_res_822_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_keys_823_, lean_object* v_i_824_, lean_object* v_k_825_){
_start:
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_array_get_size(v_keys_823_);
v___x_827_ = lean_nat_dec_lt(v_i_824_, v___x_826_);
if (v___x_827_ == 0)
{
lean_dec(v_i_824_);
return v___x_827_;
}
else
{
lean_object* v_k_x27_828_; uint8_t v___x_829_; 
v_k_x27_828_ = lean_array_fget_borrowed(v_keys_823_, v_i_824_);
v___x_829_ = l_Lean_instBEqExtraModUse_beq(v_k_825_, v_k_x27_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_add(v_i_824_, v___x_830_);
lean_dec(v_i_824_);
v_i_824_ = v___x_831_;
goto _start;
}
else
{
lean_dec(v_i_824_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_keys_833_, lean_object* v_i_834_, lean_object* v_k_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_833_, v_i_834_, v_k_835_);
lean_dec_ref(v_k_835_);
lean_dec_ref(v_keys_833_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_838_, size_t v_x_839_, lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_object* v_es_841_; lean_object* v___x_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v_j_845_; lean_object* v___x_846_; 
v_es_841_ = lean_ctor_get(v_x_838_, 0);
v___x_842_ = lean_box(2);
v___x_843_ = ((size_t)31ULL);
v___x_844_ = lean_usize_land(v_x_839_, v___x_843_);
v_j_845_ = lean_usize_to_nat(v___x_844_);
v___x_846_ = lean_array_get_borrowed(v___x_842_, v_es_841_, v_j_845_);
lean_dec(v_j_845_);
switch(lean_obj_tag(v___x_846_))
{
case 0:
{
lean_object* v_key_847_; uint8_t v___x_848_; 
v_key_847_ = lean_ctor_get(v___x_846_, 0);
v___x_848_ = l_Lean_instBEqExtraModUse_beq(v_x_840_, v_key_847_);
return v___x_848_;
}
case 1:
{
lean_object* v_node_849_; size_t v___x_850_; size_t v___x_851_; 
v_node_849_ = lean_ctor_get(v___x_846_, 0);
v___x_850_ = ((size_t)5ULL);
v___x_851_ = lean_usize_shift_right(v_x_839_, v___x_850_);
v_x_838_ = v_node_849_;
v_x_839_ = v___x_851_;
goto _start;
}
default: 
{
uint8_t v___x_853_; 
v___x_853_ = 0;
return v___x_853_;
}
}
}
else
{
lean_object* v_ks_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_ks_854_ = lean_ctor_get(v_x_838_, 0);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_ks_854_, v___x_855_, v_x_840_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
size_t v_x_8128__boxed_860_; uint8_t v_res_861_; lean_object* v_r_862_; 
v_x_8128__boxed_860_ = lean_unbox_usize(v_x_858_);
lean_dec(v_x_858_);
v_res_861_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_857_, v_x_8128__boxed_860_, v_x_859_);
lean_dec_ref(v_x_859_);
lean_dec_ref(v_x_857_);
v_r_862_ = lean_box(v_res_861_);
return v_r_862_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
uint64_t v___x_865_; size_t v___x_866_; uint8_t v___x_867_; 
v___x_865_ = l_Lean_instHashableExtraModUse_hash(v_x_864_);
v___x_866_ = lean_uint64_to_usize(v___x_865_);
v___x_867_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_863_, v___x_866_, v_x_864_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
uint8_t v_res_870_; lean_object* v_r_871_; 
v_res_870_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_868_, v_x_869_);
lean_dec_ref(v_x_869_);
lean_dec_ref(v_x_868_);
v_r_871_ = lean_box(v_res_870_);
return v_r_871_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_872_; double v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_float_of_nat(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_cls_877_, lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_ref_882_; lean_object* v___x_883_; lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_928_; 
v_ref_882_ = lean_ctor_get(v___y_879_, 2);
v___x_883_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_msg_878_, v___y_879_, v___y_880_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_928_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_928_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_928_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v_traceState_889_; lean_object* v_env_890_; lean_object* v_nextMacroScope_891_; lean_object* v_ngen_892_; lean_object* v_auxDeclNGen_893_; lean_object* v_cache_894_; lean_object* v_messages_895_; lean_object* v_infoState_896_; lean_object* v_snapshotTasks_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_927_; 
v___x_888_ = lean_st_ref_take(v___y_880_);
v_traceState_889_ = lean_ctor_get(v___x_888_, 4);
v_env_890_ = lean_ctor_get(v___x_888_, 0);
v_nextMacroScope_891_ = lean_ctor_get(v___x_888_, 1);
v_ngen_892_ = lean_ctor_get(v___x_888_, 2);
v_auxDeclNGen_893_ = lean_ctor_get(v___x_888_, 3);
v_cache_894_ = lean_ctor_get(v___x_888_, 5);
v_messages_895_ = lean_ctor_get(v___x_888_, 6);
v_infoState_896_ = lean_ctor_get(v___x_888_, 7);
v_snapshotTasks_897_ = lean_ctor_get(v___x_888_, 8);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_927_ == 0)
{
v___x_899_ = v___x_888_;
v_isShared_900_ = v_isSharedCheck_927_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_snapshotTasks_897_);
lean_inc(v_infoState_896_);
lean_inc(v_messages_895_);
lean_inc(v_cache_894_);
lean_inc(v_traceState_889_);
lean_inc(v_auxDeclNGen_893_);
lean_inc(v_ngen_892_);
lean_inc(v_nextMacroScope_891_);
lean_inc(v_env_890_);
lean_dec(v___x_888_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_927_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint64_t v_tid_901_; lean_object* v_traces_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_926_; 
v_tid_901_ = lean_ctor_get_uint64(v_traceState_889_, sizeof(void*)*1);
v_traces_902_ = lean_ctor_get(v_traceState_889_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_traceState_889_);
if (v_isSharedCheck_926_ == 0)
{
v___x_904_ = v_traceState_889_;
v_isShared_905_ = v_isSharedCheck_926_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_traces_902_);
lean_dec(v_traceState_889_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_926_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; double v___x_907_; uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_906_ = lean_box(0);
v___x_907_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_908_ = 0;
v___x_909_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_910_, 0, v_cls_877_);
lean_ctor_set(v___x_910_, 1, v___x_906_);
lean_ctor_set(v___x_910_, 2, v___x_909_);
lean_ctor_set_float(v___x_910_, sizeof(void*)*3, v___x_907_);
lean_ctor_set_float(v___x_910_, sizeof(void*)*3 + 8, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3 + 16, v___x_908_);
v___x_911_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v_a_884_);
lean_ctor_set(v___x_912_, 2, v___x_911_);
lean_inc(v_ref_882_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_ref_882_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = l_Lean_PersistentArray_push___redArg(v_traces_902_, v___x_913_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_914_);
v___x_916_ = v___x_904_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_914_);
lean_ctor_set_uint64(v_reuseFailAlloc_925_, sizeof(void*)*1, v_tid_901_);
v___x_916_ = v_reuseFailAlloc_925_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 4, v___x_916_);
v___x_918_ = v___x_899_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_env_890_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_nextMacroScope_891_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_ngen_892_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_auxDeclNGen_893_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_924_, 5, v_cache_894_);
lean_ctor_set(v_reuseFailAlloc_924_, 6, v_messages_895_);
lean_ctor_set(v_reuseFailAlloc_924_, 7, v_infoState_896_);
lean_ctor_set(v_reuseFailAlloc_924_, 8, v_snapshotTasks_897_);
v___x_918_ = v_reuseFailAlloc_924_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_919_ = lean_st_ref_put(v___y_880_, v___x_918_);
v___x_920_ = lean_box(0);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_920_);
v___x_922_ = v___x_886_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_cls_929_, lean_object* v_msg_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_929_, v_msg_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
return v_res_934_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__1));
v___x_938_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__0));
v___x_939_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_940_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__3);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__4);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__8));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__10));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15(void){
_start:
{
lean_object* v_cls_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_cls_959_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7));
v___x_960_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14));
v___x_961_ = l_Lean_Name_append(v___x_960_, v_cls_959_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__16));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__18));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_mod_972_, uint8_t v_isMeta_973_, lean_object* v_hint_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_env_979_; uint8_t v_isExporting_980_; lean_object* v___x_981_; lean_object* v_env_982_; lean_object* v___x_983_; lean_object* v_entry_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___y_989_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_978_ = lean_st_ref_get(v___y_976_);
v_env_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_979_);
lean_dec(v___x_978_);
v_isExporting_980_ = lean_ctor_get_uint8(v_env_979_, sizeof(void*)*8);
lean_dec_ref(v_env_979_);
v___x_981_ = lean_st_ref_get(v___y_976_);
v_env_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc_ref(v_env_982_);
lean_dec(v___x_981_);
v___x_983_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__2);
lean_inc(v_mod_972_);
v_entry_984_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_984_, 0, v_mod_972_);
lean_ctor_set_uint8(v_entry_984_, sizeof(void*)*1, v_isExporting_980_);
lean_ctor_set_uint8(v_entry_984_, sizeof(void*)*1 + 1, v_isMeta_973_);
v___x_985_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_986_ = lean_box(1);
v___x_987_ = lean_box(0);
v___x_1014_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_983_, v___x_985_, v_env_982_, v___x_986_, v___x_987_);
v___x_1015_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v___x_1014_, v_entry_984_);
lean_dec(v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v_toCold_1016_; lean_object* v_options_1017_; uint8_t v_hasTrace_1018_; 
v_toCold_1016_ = lean_ctor_get(v___y_975_, 0);
v_options_1017_ = lean_ctor_get(v_toCold_1016_, 2);
v_hasTrace_1018_ = lean_ctor_get_uint8(v_options_1017_, sizeof(void*)*1);
if (v_hasTrace_1018_ == 0)
{
lean_dec(v_hint_974_);
lean_dec(v_mod_972_);
v___y_989_ = v___y_976_;
goto v___jp_988_;
}
else
{
lean_object* v_inheritedTraceOptions_1019_; lean_object* v_cls_1020_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_inheritedTraceOptions_1019_ = lean_ctor_get(v_toCold_1016_, 11);
v_cls_1020_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__7));
v___x_1040_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__15);
v___x_1041_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1019_, v_options_1017_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec(v_hint_974_);
lean_dec(v_mod_972_);
v___y_989_ = v___y_976_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1042_; lean_object* v___y_1044_; 
v___x_1042_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__17);
if (v_isExporting_980_ == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__22));
v___y_1044_ = v___x_1051_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__23));
v___y_1044_ = v___x_1052_;
goto v___jp_1043_;
}
v___jp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_inc_ref(v___y_1044_);
v___x_1045_ = l_Lean_stringToMessageData(v___y_1044_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1042_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__19);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
if (v_isMeta_973_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__20));
v___y_1027_ = v___x_1048_;
v___y_1028_ = v___x_1049_;
goto v___jp_1026_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__21));
v___y_1027_ = v___x_1048_;
v___y_1028_ = v___x_1050_;
goto v___jp_1026_;
}
}
}
v___jp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___y_1022_);
lean_ctor_set(v___x_1024_, 1, v___y_1023_);
v___x_1025_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_cls_1020_, v___x_1024_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_dec_ref_known(v___x_1025_, 1);
v___y_989_ = v___y_976_;
goto v___jp_988_;
}
else
{
lean_dec_ref_known(v_entry_984_, 1);
return v___x_1025_;
}
}
v___jp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
lean_inc_ref(v___y_1028_);
v___x_1029_ = l_Lean_stringToMessageData(v___y_1028_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___y_1027_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__9);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_MessageData_ofName(v_mod_972_);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_Name_isAnonymous(v_hint_974_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__11);
v___x_1037_ = l_Lean_MessageData_ofName(v_hint_974_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___y_1022_ = v___x_1034_;
v___y_1023_ = v___x_1038_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1039_; 
lean_dec(v_hint_974_);
v___x_1039_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__12);
v___y_1022_ = v___x_1034_;
v___y_1023_ = v___x_1039_;
goto v___jp_1021_;
}
}
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref_known(v_entry_984_, 1);
lean_dec(v_hint_974_);
lean_dec(v_mod_972_);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
v___jp_988_:
{
lean_object* v___x_990_; lean_object* v_toEnvExtension_991_; lean_object* v_env_992_; lean_object* v_nextMacroScope_993_; lean_object* v_ngen_994_; lean_object* v_auxDeclNGen_995_; lean_object* v_traceState_996_; lean_object* v_messages_997_; lean_object* v_infoState_998_; lean_object* v_snapshotTasks_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1012_; 
v___x_990_ = lean_st_ref_take(v___y_989_);
v_toEnvExtension_991_ = lean_ctor_get(v___x_985_, 0);
v_env_992_ = lean_ctor_get(v___x_990_, 0);
v_nextMacroScope_993_ = lean_ctor_get(v___x_990_, 1);
v_ngen_994_ = lean_ctor_get(v___x_990_, 2);
v_auxDeclNGen_995_ = lean_ctor_get(v___x_990_, 3);
v_traceState_996_ = lean_ctor_get(v___x_990_, 4);
v_messages_997_ = lean_ctor_get(v___x_990_, 6);
v_infoState_998_ = lean_ctor_get(v___x_990_, 7);
v_snapshotTasks_999_ = lean_ctor_get(v___x_990_, 8);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_990_, 5);
lean_dec(v_unused_1013_);
v___x_1001_ = v___x_990_;
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snapshotTasks_999_);
lean_inc(v_infoState_998_);
lean_inc(v_messages_997_);
lean_inc(v_traceState_996_);
lean_inc(v_auxDeclNGen_995_);
lean_inc(v_ngen_994_);
lean_inc(v_nextMacroScope_993_);
lean_inc(v_env_992_);
lean_dec(v___x_990_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_asyncMode_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v_asyncMode_1003_ = lean_ctor_get(v_toEnvExtension_991_, 2);
v___x_1004_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_985_, v_env_992_, v_entry_984_, v_asyncMode_1003_, v___x_987_);
v___x_1005_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 5, v___x_1005_);
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1007_ = v___x_1001_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_nextMacroScope_993_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_ngen_994_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_auxDeclNGen_995_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_traceState_996_);
lean_ctor_set(v_reuseFailAlloc_1011_, 5, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1011_, 6, v_messages_997_);
lean_ctor_set(v_reuseFailAlloc_1011_, 7, v_infoState_998_);
lean_ctor_set(v_reuseFailAlloc_1011_, 8, v_snapshotTasks_999_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_st_ref_put(v___y_989_, v___x_1007_);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_mod_1055_, lean_object* v_isMeta_1056_, lean_object* v_hint_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
uint8_t v_isMeta_boxed_1061_; lean_object* v_res_1062_; 
v_isMeta_boxed_1061_ = lean_unbox(v_isMeta_1056_);
v_res_1062_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_mod_1055_, v_isMeta_boxed_1061_, v_hint_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(lean_object* v___x_1063_, lean_object* v_declName_1064_, lean_object* v_as_1065_, size_t v_sz_1066_, size_t v_i_1067_, lean_object* v_b_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_usize_dec_lt(v_i_1067_, v_sz_1066_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec(v_declName_1064_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_b_1068_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v_modules_1075_; lean_object* v___x_1076_; lean_object* v_a_1077_; lean_object* v___x_1078_; lean_object* v_toImport_1079_; lean_object* v_module_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; 
v___x_1074_ = l_Lean_Environment_header(v___x_1063_);
v_modules_1075_ = lean_ctor_get(v___x_1074_, 3);
lean_inc_ref(v_modules_1075_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1077_ = lean_array_uget_borrowed(v_as_1065_, v_i_1067_);
v___x_1078_ = lean_array_get(v___x_1076_, v_modules_1075_, v_a_1077_);
lean_dec_ref(v_modules_1075_);
v_toImport_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc_ref(v_toImport_1079_);
lean_dec(v___x_1078_);
v_module_1080_ = lean_ctor_get(v_toImport_1079_, 0);
lean_inc(v_module_1080_);
lean_dec_ref(v_toImport_1079_);
v___x_1081_ = 0;
lean_inc(v_declName_1064_);
v___x_1082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1080_, v___x_1081_, v_declName_1064_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; 
lean_dec_ref_known(v___x_1082_, 1);
v___x_1083_ = lean_box(0);
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_add(v_i_1067_, v___x_1084_);
v_i_1067_ = v___x_1085_;
v_b_1068_ = v___x_1083_;
goto _start;
}
else
{
lean_dec(v_declName_1064_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v___x_1087_, lean_object* v_declName_1088_, lean_object* v_as_1089_, lean_object* v_sz_1090_, lean_object* v_i_1091_, lean_object* v_b_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
size_t v_sz_boxed_1096_; size_t v_i_boxed_1097_; lean_object* v_res_1098_; 
v_sz_boxed_1096_ = lean_unbox_usize(v_sz_1090_);
lean_dec(v_sz_1090_);
v_i_boxed_1097_ = lean_unbox_usize(v_i_1091_);
lean_dec(v_i_1091_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v___x_1087_, v_declName_1088_, v_as_1089_, v_sz_boxed_1096_, v_i_boxed_1097_, v_b_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec_ref(v_as_1089_);
lean_dec_ref(v___x_1087_);
return v_res_1098_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__2(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__1));
v___x_1102_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__0));
v___x_1103_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1102_, v___x_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(lean_object* v_declName_1106_, uint8_t v_isMeta_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1115_; lean_object* v___y_1117_; lean_object* v___x_1130_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1115_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1115_);
lean_dec(v___x_1111_);
v___x_1130_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1115_, v_declName_1106_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_dec_ref(v_env_1115_);
lean_dec(v_declName_1106_);
goto v___jp_1112_;
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1132_; lean_object* v_modules_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_val_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = l_Lean_Environment_header(v_env_1115_);
v_modules_1133_ = lean_ctor_get(v___x_1132_, 3);
lean_inc_ref(v_modules_1133_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = lean_array_get_size(v_modules_1133_);
v___x_1135_ = lean_nat_dec_lt(v_val_1131_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_dec_ref(v_modules_1133_);
lean_dec(v_val_1131_);
lean_dec_ref(v_env_1115_);
lean_dec(v_declName_1106_);
goto v___jp_1112_;
}
else
{
lean_object* v___x_1136_; lean_object* v_env_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___y_1141_; 
v___x_1136_ = lean_st_ref_get(v___y_1109_);
v_env_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc_ref(v_env_1137_);
lean_dec(v___x_1136_);
v___x_1138_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__2);
v___x_1139_ = lean_array_fget(v_modules_1133_, v_val_1131_);
lean_dec(v_val_1131_);
lean_dec_ref(v_modules_1133_);
if (v_isMeta_1107_ == 0)
{
lean_dec_ref(v_env_1137_);
v___y_1141_ = v_isMeta_1107_;
goto v___jp_1140_;
}
else
{
uint8_t v___x_1152_; 
lean_inc(v_declName_1106_);
v___x_1152_ = l_Lean_isMarkedMeta(v_env_1137_, v_declName_1106_);
if (v___x_1152_ == 0)
{
v___y_1141_ = v_isMeta_1107_;
goto v___jp_1140_;
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = 0;
v___y_1141_ = v___x_1153_;
goto v___jp_1140_;
}
}
v___jp_1140_:
{
lean_object* v_toImport_1142_; lean_object* v_module_1143_; lean_object* v___x_1144_; 
v_toImport_1142_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_ref(v_toImport_1142_);
lean_dec(v___x_1139_);
v_module_1143_ = lean_ctor_get(v_toImport_1142_, 0);
lean_inc(v_module_1143_);
lean_dec_ref(v_toImport_1142_);
lean_inc(v_declName_1106_);
v___x_1144_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2(v_module_1143_, v___y_1141_, v_declName_1106_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref_known(v___x_1144_, 1);
v___x_1145_ = l_Lean_indirectModUseExt;
v___x_1146_ = lean_box(1);
v___x_1147_ = lean_box(0);
lean_inc_ref(v_env_1115_);
v___x_1148_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1138_, v___x_1145_, v_env_1115_, v___x_1146_, v___x_1147_);
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v___x_1148_, v_declName_1106_);
lean_dec(v___x_1148_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___closed__3));
v___y_1117_ = v___x_1150_;
goto v___jp_1116_;
}
else
{
lean_object* v_val_1151_; 
v_val_1151_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v___x_1149_, 1);
v___y_1117_ = v_val_1151_;
goto v___jp_1116_;
}
}
else
{
lean_dec_ref(v_env_1115_);
lean_dec(v_declName_1106_);
return v___x_1144_;
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
v___jp_1116_:
{
lean_object* v___x_1118_; size_t v_sz_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
v___x_1118_ = lean_box(0);
v_sz_1119_ = lean_array_size(v___y_1117_);
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__3(v_env_1115_, v_declName_1106_, v___y_1117_, v_sz_1119_, v___x_1120_, v___x_1118_, v___y_1108_, v___y_1109_);
lean_dec_ref(v___y_1117_);
lean_dec_ref(v_env_1115_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1121_, 0);
lean_dec(v_unused_1129_);
v___x_1123_ = v___x_1121_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_dec(v___x_1121_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1118_);
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1118_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1___boxed(lean_object* v_declName_1154_, lean_object* v_isMeta_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v_isMeta_boxed_1159_; lean_object* v_res_1160_; 
v_isMeta_boxed_1159_ = lean_unbox(v_isMeta_1155_);
v_res_1160_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_declName_1154_, v_isMeta_boxed_1159_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1160_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1167_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1170_ = lean_box(1);
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg___closed__4);
v___x_1172_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___x_1171_);
lean_ctor_set(v___x_1173_, 2, v___x_1170_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(uint8_t v_x_1174_, lean_object* v_stx_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1175_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1262_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1262_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1262_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v_infoState_1185_; uint8_t v_enabled_1186_; lean_object* v___x_1187_; 
v___x_1184_ = lean_st_ref_get(v___y_1177_);
v_infoState_1185_ = lean_ctor_get(v___x_1184_, 7);
lean_inc_ref(v_infoState_1185_);
lean_dec(v___x_1184_);
v_enabled_1186_ = lean_ctor_get_uint8(v_infoState_1185_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1185_);
v___x_1187_ = l_Lean_Syntax_getId(v_a_1180_);
if (v_enabled_1186_ == 0)
{
lean_object* v___x_1189_; 
lean_dec(v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1187_);
v___x_1189_ = v___x_1182_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Lean_Name_isAtomic(v___x_1187_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1192_ = l_Lean_Name_getRoot(v___x_1187_);
v___x_1193_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1194_ = lean_name_eq(v___x_1192_, v___x_1193_);
lean_dec(v___x_1192_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1196_; 
lean_dec(v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1187_);
v___x_1196_ = v___x_1182_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1187_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___y_1201_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_del_object(v___x_1182_);
v___x_1198_ = lean_box(0);
lean_inc(v___x_1187_);
v___x_1199_ = l_Lean_Name_replacePrefix(v___x_1187_, v___x_1193_, v___x_1198_);
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Lean_Syntax_identComponents(v_a_1180_, v___x_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
v___y_1201_ = v___x_1257_;
goto v___jp_1200_;
}
else
{
lean_object* v_tail_1258_; 
v_tail_1258_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_tail_1258_);
lean_dec_ref_known(v___x_1257_, 2);
v___y_1201_ = v_tail_1258_;
goto v___jp_1200_;
}
v___jp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1202_ = lean_array_mk(v___y_1201_);
v___x_1203_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1204_ = lean_box(2);
v___x_1205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set(v___x_1205_, 1, v___x_1203_);
lean_ctor_set(v___x_1205_, 2, v___x_1202_);
lean_inc_n(v___x_1199_, 2);
v___x_1206_ = l_Lean_mkIdentFrom(v___x_1205_, v___x_1199_, v_enabled_1186_);
lean_dec_ref_known(v___x_1205_, 3);
v___x_1207_ = lean_obj_once(&l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_, &l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__once, _init_l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_);
v___x_1208_ = lean_box(0);
lean_inc(v___x_1206_);
v___x_1209_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1209_, 0, v___x_1206_);
lean_ctor_set(v___x_1209_, 1, v___x_1199_);
lean_ctor_set(v___x_1209_, 2, v___x_1207_);
lean_ctor_set(v___x_1209_, 3, v___x_1208_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*4, v___x_1191_);
v___x_1210_ = l_Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0(v___x_1209_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1246_; 
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1247_);
v___x_1212_ = v___x_1210_;
v_isShared_1213_ = v_isSharedCheck_1246_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v___x_1210_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1246_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v_env_1215_; uint8_t v___x_1216_; 
v___x_1214_ = lean_st_ref_get(v___y_1177_);
v_env_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc_ref(v_env_1215_);
lean_dec(v___x_1214_);
lean_inc(v___x_1199_);
v___x_1216_ = l_Lean_Environment_contains(v_env_1215_, v___x_1199_, v_enabled_1186_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1218_; 
lean_dec(v___x_1206_);
lean_dec(v___x_1199_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1187_);
v___x_1218_ = v___x_1212_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1187_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
else
{
lean_object* v___x_1220_; 
lean_del_object(v___x_1212_);
lean_inc(v___x_1199_);
v___x_1220_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v___x_1199_, v___x_1191_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1221_; 
lean_dec_ref_known(v___x_1220_, 1);
v___x_1221_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2(v___x_1206_, v___x_1199_, v___x_1208_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1229_);
v___x_1223_ = v___x_1221_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v___x_1221_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1187_);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1187_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v___x_1187_);
v_a_1230_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1221_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1221_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v___x_1206_);
lean_dec(v___x_1199_);
lean_dec(v___x_1187_);
v_a_1238_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1220_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1220_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v___x_1206_);
lean_dec(v___x_1199_);
lean_dec(v___x_1187_);
v_a_1248_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1210_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1210_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
else
{
lean_object* v___x_1260_; 
lean_dec(v_a_1180_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1187_);
v___x_1260_ = v___x_1182_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1187_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1179_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1179_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_x_1271_, lean_object* v_stx_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v_x_8698__boxed_1276_; lean_object* v_res_1277_; 
v_x_8698__boxed_1276_ = lean_unbox(v_x_1271_);
v_res_1277_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(v_x_8698__boxed_1276_, v_stx_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__12_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1311_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1312_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_1310_, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2____boxed(lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_();
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_t_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_t_1315_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_t_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addCompletionInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_t_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_1325_, lean_object* v_m_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___redArg(v_m_1326_, v_a_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_1329_, lean_object* v_m_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_1329_, v_m_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_m_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_x_1334_, v_x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
uint8_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_1337_, v_x_1338_, v_x_1339_);
lean_dec_ref(v_x_1339_);
lean_dec_ref(v_x_1338_);
v_r_1341_ = lean_box(v_res_1340_);
return v_r_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(lean_object* v_00_u03b2_1342_, lean_object* v_a_1343_, lean_object* v_x_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_a_1343_, v_x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1346_, lean_object* v_a_1347_, lean_object* v_x_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__4_spec__8(v_00_u03b2_1346_, v_a_1347_, v_x_1348_);
lean_dec(v_x_1348_);
lean_dec(v_a_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_1350_, lean_object* v_x_1351_, size_t v_x_1352_, lean_object* v_x_1353_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___redArg(v_x_1351_, v_x_1352_, v_x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
size_t v_x_9034__boxed_1359_; uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_x_9034__boxed_1359_ = lean_unbox_usize(v_x_1357_);
lean_dec(v_x_1357_);
v_res_1360_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6(v_00_u03b2_1355_, v_x_1356_, v_x_9034__boxed_1359_, v_x_1358_);
lean_dec_ref(v_x_1358_);
lean_dec_ref(v_x_1356_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(lean_object* v_00_u03b1_1362_, lean_object* v_constName_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___redArg(v_constName_1363_, v___y_1364_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14(v_00_u03b1_1368_, v_constName_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_1374_, lean_object* v_keys_1375_, lean_object* v_vals_1376_, lean_object* v_heq_1377_, lean_object* v_i_1378_, lean_object* v_k_1379_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___redArg(v_keys_1375_, v_i_1378_, v_k_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1381_, lean_object* v_keys_1382_, lean_object* v_vals_1383_, lean_object* v_heq_1384_, lean_object* v_i_1385_, lean_object* v_k_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__6_spec__10(v_00_u03b2_1381_, v_keys_1382_, v_vals_1383_, v_heq_1384_, v_i_1385_, v_k_1386_);
lean_dec_ref(v_k_1386_);
lean_dec_ref(v_vals_1383_);
lean_dec_ref(v_keys_1382_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(lean_object* v_00_u03b1_1389_, lean_object* v_ref_1390_, lean_object* v_constName_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg(v_ref_1390_, v_constName_1391_, v___y_1392_, v___y_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1396_, lean_object* v_ref_1397_, lean_object* v_constName_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16(v_00_u03b1_1396_, v_ref_1397_, v_constName_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v_ref_1397_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1403_, lean_object* v_ref_1404_, lean_object* v_msg_1405_, lean_object* v_declHint_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___redArg(v_ref_1404_, v_msg_1405_, v_declHint_1406_, v___y_1407_, v___y_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1411_, lean_object* v_ref_1412_, lean_object* v_msg_1413_, lean_object* v_declHint_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18(v_00_u03b1_1411_, v_ref_1412_, v_msg_1413_, v_declHint_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v_ref_1412_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(lean_object* v_msg_1419_, lean_object* v_declHint_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___redArg(v_msg_1419_, v_declHint_1420_, v___y_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20___boxed(lean_object* v_msg_1425_, lean_object* v_declHint_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__19_spec__20(v_msg_1425_, v_declHint_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(lean_object* v_00_u03b1_1431_, lean_object* v_ref_1432_, lean_object* v_msg_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___redArg(v_ref_1432_, v_msg_1433_, v___y_1434_, v___y_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_00_u03b1_1438_, lean_object* v_ref_1439_, lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20(v_00_u03b1_1438_, v_ref_1439_, v_msg_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v_ref_1439_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_00_u03b1_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___redArg(v_msg_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16_spec__18_spec__20_spec__22(v_00_u03b1_1451_, v_msg_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1(){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1460_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___closed__0));
v___x_1461_ = l_Lean_addBuiltinDocString(v___x_1459_, v___x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1___boxed(lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3(){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__14_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1491_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___closed__6));
v___x_1492_ = l_Lean_addBuiltinDeclarationRanges(v___x_1490_, v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3___boxed(lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(lean_object* v___x_1523_, uint8_t v___x_1524_, lean_object* v_id_1525_, lean_object* v_x_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1529_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___closed__0));
v___x_1530_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1523_, v___x_1524_);
v___x_1531_ = lean_string_append(v___x_1529_, v___x_1530_);
lean_dec_ref(v___x_1530_);
v___x_1532_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1533_ = lean_string_append(v___x_1531_, v___x_1532_);
v___x_1534_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1525_, v___x_1533_, v___y_1527_, v___y_1528_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0___boxed(lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v_id_1537_, lean_object* v_x_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___x_2294__boxed_1541_; lean_object* v_res_1542_; 
v___x_2294__boxed_1541_ = lean_unbox(v___x_1536_);
v_res_1542_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1535_, v___x_2294__boxed_1541_, v_id_1537_, v_x_1538_, v___y_1539_, v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v_x_1538_);
lean_dec(v_id_1537_);
return v_res_1542_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1553_ = l_String_toRawSubstring_x27(v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(lean_object* v_x_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___y_1558_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_attrApp__delab___00__closed__1));
lean_inc(v_x_1554_);
v___x_1578_ = l_Lean_Syntax_isOfKind(v_x_1554_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v_x_1554_);
v___x_1579_ = lean_box(1);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v_a_1556_);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; lean_object* v_id_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1581_ = lean_unsigned_to_nat(1u);
v_id_1582_ = l_Lean_Syntax_getArg(v_x_1554_, v___x_1581_);
lean_dec(v_x_1554_);
v___x_1583_ = l_Lean_TSyntax_getId(v_id_1582_);
lean_inc(v___x_1583_);
v___x_1584_ = l_Lean_Macro_resolveGlobalName(v___x_1583_, v_a_1555_, v_a_1556_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
if (lean_obj_tag(v_a_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1586_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1584_, 2);
v___x_1587_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__0));
v___x_1588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1583_, v___x_1578_);
v___x_1589_ = lean_string_append(v___x_1587_, v___x_1588_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__2));
v___x_1591_ = lean_string_append(v___x_1589_, v___x_1590_);
v___x_1592_ = l_Lean_Macro_throwErrorAt___redArg(v_id_1582_, v___x_1591_, v_a_1555_, v_a_1586_);
lean_dec(v_id_1582_);
v___y_1558_ = v___x_1592_;
goto v___jp_1557_;
}
else
{
lean_object* v_head_1593_; lean_object* v_snd_1594_; 
v_head_1593_ = lean_ctor_get(v_a_1585_, 0);
v_snd_1594_ = lean_ctor_get(v_head_1593_, 1);
if (lean_obj_tag(v_snd_1594_) == 0)
{
lean_object* v_tail_1595_; 
v_tail_1595_ = lean_ctor_get(v_a_1585_, 1);
if (lean_obj_tag(v_tail_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1621_; 
lean_inc(v_head_1593_);
lean_dec_ref_known(v_a_1585_, 2);
lean_dec(v___x_1583_);
v_a_1596_ = lean_ctor_get(v___x_1584_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v___x_1584_, 0);
lean_dec(v_unused_1622_);
v___x_1598_ = v___x_1584_;
v_isShared_1599_ = v_isSharedCheck_1621_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1584_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1621_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v_fst_1600_; lean_object* v_quotContext_1601_; lean_object* v_currMacroScope_1602_; lean_object* v_ref_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
v_fst_1600_ = lean_ctor_get(v_head_1593_, 0);
lean_inc(v_fst_1600_);
lean_dec(v_head_1593_);
v_quotContext_1601_ = lean_ctor_get(v_a_1555_, 1);
v_currMacroScope_1602_ = lean_ctor_get(v_a_1555_, 2);
v_ref_1603_ = lean_ctor_get(v_a_1555_, 5);
v___x_1604_ = 0;
v___x_1605_ = l_Lean_SourceInfo_fromRef(v_ref_1603_, v___x_1604_);
v___x_1606_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__4));
v___x_1607_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5, &l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5_once, _init_l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___closed__5);
v___x_1608_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__5_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
lean_inc(v_currMacroScope_1602_);
lean_inc(v_quotContext_1601_);
v___x_1609_ = l_Lean_addMacroScope(v_quotContext_1601_, v___x_1608_, v_currMacroScope_1602_);
v___x_1610_ = lean_box(0);
lean_inc_n(v___x_1605_, 2);
v___x_1611_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1605_);
lean_ctor_set(v___x_1611_, 1, v___x_1607_);
lean_ctor_set(v___x_1611_, 2, v___x_1609_);
lean_ctor_set(v___x_1611_, 3, v___x_1610_);
v___x_1612_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1613_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1614_ = l_Lean_Name_append(v___x_1613_, v_fst_1600_);
v___x_1615_ = l_Lean_mkIdentFrom(v_id_1582_, v___x_1614_, v___x_1578_);
lean_dec(v_id_1582_);
v___x_1616_ = l_Lean_Syntax_node1(v___x_1605_, v___x_1612_, v___x_1615_);
v___x_1617_ = l_Lean_Syntax_node2(v___x_1605_, v___x_1606_, v___x_1611_, v___x_1616_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1617_);
v___x_1619_ = v___x_1598_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1596_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1584_, 2);
v___x_1624_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1583_, v___x_1578_, v_id_1582_, v_a_1585_, v_a_1555_, v_a_1623_);
lean_dec_ref_known(v_a_1585_, 2);
lean_dec(v_id_1582_);
v___y_1558_ = v___x_1624_;
goto v___jp_1557_;
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1584_, 2);
v___x_1626_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___lam__0(v___x_1583_, v___x_1578_, v_id_1582_, v_a_1585_, v_a_1555_, v_a_1625_);
lean_dec_ref_known(v_a_1585_, 2);
lean_dec(v_id_1582_);
v___y_1558_ = v___x_1626_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v___x_1583_);
lean_dec(v_id_1582_);
v_a_1627_ = lean_ctor_get(v___x_1584_, 0);
v_a_1628_ = lean_ctor_get(v___x_1584_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1584_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_inc(v_a_1627_);
lean_dec(v___x_1584_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1627_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
v___jp_1557_:
{
if (lean_obj_tag(v___y_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1559_ = lean_ctor_get(v___y_1558_, 0);
v_a_1560_ = lean_ctor_get(v___y_1558_, 1);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___y_1558_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___y_1558_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_inc(v_a_1559_);
lean_dec(v___y_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1559_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1568_ = lean_ctor_get(v___y_1558_, 0);
v_a_1569_ = lean_ctor_get(v___y_1558_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___y_1558_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___y_1558_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_inc(v_a_1568_);
lean_dec(v___y_1558_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1568_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1___boxed(lean_object* v_x_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_PrettyPrinter_Delaborator___aux__Lean__PrettyPrinter__Delaborator__Basic______macroRules__Lean__PrettyPrinter__Delaborator__attrApp__delab____1(v_x_1636_, v_a_1637_, v_a_1638_);
lean_dec_ref(v_a_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(lean_object* v___y_1640_){
_start:
{
lean_object* v_subExpr_1642_; lean_object* v_expr_1643_; lean_object* v___x_1644_; 
v_subExpr_1642_ = lean_ctor_get(v___y_1640_, 3);
v_expr_1643_ = lean_ctor_get(v_subExpr_1642_, 0);
lean_inc_ref(v_expr_1643_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_expr_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg___boxed(lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1645_);
lean_dec_ref(v___y_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_1648_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___boxed(lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0(v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(lean_object* v_c_1664_, lean_object* v_us_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_1667_ = l_Lean_Name_append(v___x_1666_, v_c_1664_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0___boxed(lean_object* v_c_1668_, lean_object* v_us_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_c_1668_, v_us_1669_);
lean_dec(v_us_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(lean_object* v_x_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___boxed(lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_x_1676_);
lean_dec(v_x_1676_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1712_; lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1788_; 
v___x_1712_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_1705_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1788_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1788_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
switch(lean_obj_tag(v_a_1713_))
{
case 0:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_dec_ref_known(v_a_1713_, 1);
v___x_1717_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
case 1:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
lean_dec_ref_known(v_a_1713_, 1);
v___x_1721_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1721_);
v___x_1723_ = v___x_1715_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
case 2:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_dec_ref_known(v_a_1713_, 1);
v___x_1725_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1725_);
v___x_1727_ = v___x_1715_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
case 3:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_dec_ref_known(v_a_1713_, 1);
v___x_1729_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1729_);
v___x_1731_ = v___x_1715_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
case 4:
{
lean_object* v_declName_1733_; lean_object* v_us_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v_declName_1733_ = lean_ctor_get(v_a_1713_, 0);
lean_inc(v_declName_1733_);
v_us_1734_ = lean_ctor_get(v_a_1713_, 1);
lean_inc(v_us_1734_);
lean_dec_ref_known(v_a_1713_, 2);
v___x_1735_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1733_, v_us_1734_);
lean_dec(v_us_1734_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1735_);
v___x_1737_ = v___x_1715_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
case 5:
{
lean_object* v_fn_1739_; lean_object* v___x_1740_; 
v_fn_1739_ = lean_ctor_get(v_a_1713_, 0);
lean_inc_ref(v_fn_1739_);
lean_dec_ref_known(v_a_1713_, 2);
v___x_1740_ = l_Lean_Expr_getAppFn(v_fn_1739_);
lean_dec_ref(v_fn_1739_);
if (lean_obj_tag(v___x_1740_) == 4)
{
lean_object* v_declName_1741_; lean_object* v_us_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v_declName_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_declName_1741_);
v_us_1742_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_us_1742_);
lean_dec_ref_known(v___x_1740_, 2);
v___x_1743_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__0(v_declName_1741_, v_us_1742_);
lean_dec(v_us_1742_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1743_);
v___x_1745_ = v___x_1715_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec_ref(v___x_1740_);
v___x_1747_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1747_);
v___x_1749_ = v___x_1715_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
case 6:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_dec_ref_known(v_a_1713_, 3);
v___x_1751_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1751_);
v___x_1753_ = v___x_1715_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
case 7:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec_ref_known(v_a_1713_, 3);
v___x_1755_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1755_);
v___x_1757_ = v___x_1715_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
case 8:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec_ref_known(v_a_1713_, 4);
v___x_1759_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1759_);
v___x_1761_ = v___x_1715_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
case 9:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec_ref_known(v_a_1713_, 1);
v___x_1763_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1763_);
v___x_1765_ = v___x_1715_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
case 10:
{
lean_object* v_data_1767_; 
v_data_1767_ = lean_ctor_get(v_a_1713_, 0);
lean_inc(v_data_1767_);
lean_dec_ref_known(v_a_1713_, 2);
if (lean_obj_tag(v_data_1767_) == 1)
{
lean_object* v_tail_1768_; 
v_tail_1768_ = lean_ctor_get(v_data_1767_, 1);
if (lean_obj_tag(v_tail_1768_) == 0)
{
lean_object* v_head_1769_; lean_object* v_fst_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v_head_1769_ = lean_ctor_get(v_data_1767_, 0);
lean_inc(v_head_1769_);
lean_dec_ref_known(v_data_1767_, 2);
v_fst_1770_ = lean_ctor_get(v_head_1769_, 0);
lean_inc(v_fst_1770_);
lean_dec(v_head_1769_);
v___x_1771_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1___closed__1));
v___x_1772_ = l_Lean_Name_append(v___x_1771_, v_fst_1770_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1772_);
v___x_1774_ = v___x_1715_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1767_);
lean_dec_ref_known(v_data_1767_, 2);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1776_);
v___x_1778_ = v___x_1715_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = l_Lean_PrettyPrinter_Delaborator_getExprKind___lam__1(v_data_1767_);
lean_dec(v_data_1767_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1780_);
v___x_1782_ = v___x_1715_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
default: 
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec_ref_known(v_a_1713_, 3);
v___x_1784_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17));
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1784_);
v___x_1786_ = v___x_1715_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(lean_object* v_o_1797_, lean_object* v_k_1798_, lean_object* v_v_1799_){
_start:
{
lean_object* v_map_1800_; uint8_t v_hasTrace_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1814_; 
v_map_1800_ = lean_ctor_get(v_o_1797_, 0);
v_hasTrace_1801_ = lean_ctor_get_uint8(v_o_1797_, sizeof(void*)*1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_o_1797_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1803_ = v_o_1797_;
v_isShared_1804_ = v_isSharedCheck_1814_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_map_1800_);
lean_dec(v_o_1797_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1814_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; 
lean_inc(v_k_1798_);
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1798_, v_v_1799_, v_map_1800_);
if (v_hasTrace_1801_ == 0)
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1809_; 
v___x_1806_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14));
v___x_1807_ = l_Lean_Name_isPrefixOf(v___x_1806_, v_k_1798_);
lean_dec(v_k_1798_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v___x_1809_ = v___x_1803_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1805_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*1, v___x_1807_);
return v___x_1809_;
}
}
else
{
lean_object* v___x_1812_; 
lean_dec(v_k_1798_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v___x_1812_ = v___x_1803_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*1, v_hasTrace_1801_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(lean_object* v___y_1815_){
_start:
{
lean_object* v_subExpr_1817_; lean_object* v_pos_1818_; lean_object* v___x_1819_; 
v_subExpr_1817_ = lean_ctor_get(v___y_1815_, 3);
v_pos_1818_ = lean_ctor_get(v_subExpr_1817_, 1);
lean_inc(v_pos_1818_);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_pos_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg___boxed(lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1820_);
lean_dec_ref(v___y_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v___y_1823_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___boxed(lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1(v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(lean_object* v_t_1839_, lean_object* v_k_1840_){
_start:
{
if (lean_obj_tag(v_t_1839_) == 0)
{
lean_object* v_k_1841_; lean_object* v_v_1842_; lean_object* v_l_1843_; lean_object* v_r_1844_; uint8_t v___x_1845_; 
v_k_1841_ = lean_ctor_get(v_t_1839_, 1);
v_v_1842_ = lean_ctor_get(v_t_1839_, 2);
v_l_1843_ = lean_ctor_get(v_t_1839_, 3);
v_r_1844_ = lean_ctor_get(v_t_1839_, 4);
v___x_1845_ = lean_nat_dec_lt(v_k_1840_, v_k_1841_);
if (v___x_1845_ == 0)
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_nat_dec_eq(v_k_1840_, v_k_1841_);
if (v___x_1846_ == 0)
{
v_t_1839_ = v_r_1844_;
goto _start;
}
else
{
lean_object* v___x_1848_; 
lean_inc(v_v_1842_);
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_v_1842_);
return v___x_1848_;
}
}
else
{
v_t_1839_ = v_l_1843_;
goto _start;
}
}
else
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_box(0);
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg___boxed(lean_object* v_t_1851_, lean_object* v_k_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1851_, v_k_1852_);
lean_dec(v_k_1852_);
lean_dec(v_t_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(lean_object* v_init_1854_, lean_object* v_x_1855_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
lean_object* v_k_1857_; lean_object* v_v_1858_; lean_object* v_l_1859_; lean_object* v_r_1860_; lean_object* v___x_1861_; lean_object* v_a_1862_; lean_object* v_a_1863_; lean_object* v___x_1864_; 
v_k_1857_ = lean_ctor_get(v_x_1855_, 1);
lean_inc(v_k_1857_);
v_v_1858_ = lean_ctor_get(v_x_1855_, 2);
lean_inc(v_v_1858_);
v_l_1859_ = lean_ctor_get(v_x_1855_, 3);
lean_inc(v_l_1859_);
v_r_1860_ = lean_ctor_get(v_x_1855_, 4);
lean_inc(v_r_1860_);
lean_dec_ref_known(v_x_1855_, 5);
v___x_1861_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1854_, v_l_1859_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___x_1861_);
v_a_1863_ = lean_ctor_get(v_a_1862_, 0);
lean_inc(v_a_1863_);
lean_dec(v_a_1862_);
v___x_1864_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v_a_1863_, v_k_1857_, v_v_1858_);
v_init_1854_ = v___x_1864_;
v_x_1855_ = v_r_1860_;
goto _start;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_init_1854_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg___boxed(lean_object* v_init_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1868_, v_x_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_toCold_1879_; lean_object* v___x_1880_; lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1903_; 
v_toCold_1879_ = lean_ctor_get(v_a_1876_, 0);
v___x_1880_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_1872_);
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1903_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1903_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_options_1885_; lean_object* v_optionsPerPos_1886_; lean_object* v___x_1887_; 
v_options_1885_ = lean_ctor_get(v_toCold_1879_, 2);
v_optionsPerPos_1886_ = lean_ctor_get(v_a_1872_, 0);
v___x_1887_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_1886_, v_a_1881_);
lean_dec(v_a_1881_);
if (lean_obj_tag(v___x_1887_) == 1)
{
lean_object* v_val_1888_; lean_object* v_map_1889_; lean_object* v___x_1890_; lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1899_; 
lean_del_object(v___x_1883_);
v_val_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v_map_1889_ = lean_ctor_get(v_val_1888_, 0);
lean_inc(v_map_1889_);
lean_dec(v_val_1888_);
lean_inc_ref(v_options_1885_);
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_options_1885_, v_map_1889_);
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1899_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_a_1895_; lean_object* v___x_1897_; 
v_a_1895_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_a_1895_);
lean_dec(v_a_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_a_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v___x_1901_; 
lean_dec(v___x_1887_);
lean_inc_ref(v_options_1885_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v_options_1885_);
v___x_1901_ = v___x_1883_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_options_1885_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___boxed(lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(lean_object* v_00_u03b4_1912_, lean_object* v_t_1913_, lean_object* v_k_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_t_1913_, v_k_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___boxed(lean_object* v_00_u03b4_1916_, lean_object* v_t_1917_, lean_object* v_k_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2(v_00_u03b4_1916_, v_t_1917_, v_k_1918_);
lean_dec(v_k_1918_);
lean_dec(v_t_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(lean_object* v_init_1920_, lean_object* v_x_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___redArg(v_init_1920_, v_x_1921_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3___boxed(lean_object* v_init_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__3(v_init_1930_, v_x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(lean_object* v_opt_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_apply_1(v_opt_1940_, v_a_1949_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_opt_1940_);
v_a_1958_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1948_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1948_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg___boxed(lean_object* v_opt_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* v_00_u03b1_1975_, lean_object* v_opt_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* v_00_u03b1_1985_, lean_object* v_opt_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_PrettyPrinter_Delaborator_getPPOption(v_00_u03b1_1985_, v_opt_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* v_opt_1995_, lean_object* v_d_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_1995_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; uint8_t v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
lean_dec_ref(v_d_1996_);
v___x_2007_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; 
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc_ref(v_a_1997_);
v___x_2008_ = lean_apply_7(v_d_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, lean_box(0));
return v___x_2008_;
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec_ref(v_d_1996_);
v_a_2009_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2004_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2004_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption___boxed(lean_object* v_opt_2017_, lean_object* v_d_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_PrettyPrinter_Delaborator_whenPPOption(v_opt_2017_, v_d_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* v_opt_2027_, lean_object* v_d_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v_opt_2027_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; uint8_t v___x_2038_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___x_2038_ = lean_unbox(v_a_2037_);
lean_dec(v_a_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_inc(v_a_2034_);
lean_inc_ref(v_a_2033_);
lean_inc(v_a_2032_);
lean_inc_ref(v_a_2031_);
lean_inc(v_a_2030_);
lean_inc_ref(v_a_2029_);
v___x_2039_ = lean_apply_7(v_d_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, lean_box(0));
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; 
lean_dec_ref(v_d_2028_);
v___x_2040_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_2040_;
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_d_2028_);
v_a_2041_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2036_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2036_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption___boxed(lean_object* v_opt_2049_, lean_object* v_d_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(v_opt_2049_, v_d_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(lean_object* v_k_2059_, lean_object* v_v_2060_, lean_object* v_t_2061_){
_start:
{
if (lean_obj_tag(v_t_2061_) == 0)
{
lean_object* v_size_2062_; lean_object* v_k_2063_; lean_object* v_v_2064_; lean_object* v_l_2065_; lean_object* v_r_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2347_; 
v_size_2062_ = lean_ctor_get(v_t_2061_, 0);
v_k_2063_ = lean_ctor_get(v_t_2061_, 1);
v_v_2064_ = lean_ctor_get(v_t_2061_, 2);
v_l_2065_ = lean_ctor_get(v_t_2061_, 3);
v_r_2066_ = lean_ctor_get(v_t_2061_, 4);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_t_2061_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2068_ = v_t_2061_;
v_isShared_2069_ = v_isSharedCheck_2347_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_r_2066_);
lean_inc(v_l_2065_);
lean_inc(v_v_2064_);
lean_inc(v_k_2063_);
lean_inc(v_size_2062_);
lean_dec(v_t_2061_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2347_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_nat_dec_lt(v_k_2059_, v_k_2063_);
if (v___x_2070_ == 0)
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_nat_dec_eq(v_k_2059_, v_k_2063_);
if (v___x_2071_ == 0)
{
lean_object* v_impl_2072_; lean_object* v___x_2073_; 
lean_dec(v_size_2062_);
v_impl_2072_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2059_, v_v_2060_, v_r_2066_);
v___x_2073_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2065_) == 0)
{
lean_object* v_size_2074_; lean_object* v_size_2075_; lean_object* v_k_2076_; lean_object* v_v_2077_; lean_object* v_l_2078_; lean_object* v_r_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_size_2074_ = lean_ctor_get(v_l_2065_, 0);
v_size_2075_ = lean_ctor_get(v_impl_2072_, 0);
lean_inc(v_size_2075_);
v_k_2076_ = lean_ctor_get(v_impl_2072_, 1);
lean_inc(v_k_2076_);
v_v_2077_ = lean_ctor_get(v_impl_2072_, 2);
lean_inc(v_v_2077_);
v_l_2078_ = lean_ctor_get(v_impl_2072_, 3);
lean_inc(v_l_2078_);
v_r_2079_ = lean_ctor_get(v_impl_2072_, 4);
lean_inc(v_r_2079_);
v___x_2080_ = lean_unsigned_to_nat(3u);
v___x_2081_ = lean_nat_mul(v___x_2080_, v_size_2074_);
v___x_2082_ = lean_nat_dec_lt(v___x_2081_, v_size_2075_);
lean_dec(v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_r_2079_);
lean_dec(v_l_2078_);
lean_dec(v_v_2077_);
lean_dec(v_k_2076_);
v___x_2083_ = lean_nat_add(v___x_2073_, v_size_2074_);
v___x_2084_ = lean_nat_add(v___x_2083_, v_size_2075_);
lean_dec(v_size_2075_);
lean_dec(v___x_2083_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_impl_2072_);
lean_ctor_set(v___x_2068_, 0, v___x_2084_);
v___x_2086_ = v___x_2068_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_l_2065_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_impl_2072_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
else
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2151_; 
v_isSharedCheck_2151_ = !lean_is_exclusive(v_impl_2072_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; lean_object* v_unused_2153_; lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; 
v_unused_2152_ = lean_ctor_get(v_impl_2072_, 4);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_impl_2072_, 3);
lean_dec(v_unused_2153_);
v_unused_2154_ = lean_ctor_get(v_impl_2072_, 2);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_impl_2072_, 1);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_impl_2072_, 0);
lean_dec(v_unused_2156_);
v___x_2089_ = v_impl_2072_;
v_isShared_2090_ = v_isSharedCheck_2151_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v_impl_2072_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2151_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_size_2091_; lean_object* v_k_2092_; lean_object* v_v_2093_; lean_object* v_l_2094_; lean_object* v_r_2095_; lean_object* v_size_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_size_2091_ = lean_ctor_get(v_l_2078_, 0);
v_k_2092_ = lean_ctor_get(v_l_2078_, 1);
v_v_2093_ = lean_ctor_get(v_l_2078_, 2);
v_l_2094_ = lean_ctor_get(v_l_2078_, 3);
v_r_2095_ = lean_ctor_get(v_l_2078_, 4);
v_size_2096_ = lean_ctor_get(v_r_2079_, 0);
v___x_2097_ = lean_unsigned_to_nat(2u);
v___x_2098_ = lean_nat_mul(v___x_2097_, v_size_2096_);
v___x_2099_ = lean_nat_dec_lt(v_size_2091_, v___x_2098_);
lean_dec(v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2127_; 
lean_inc(v_r_2095_);
lean_inc(v_l_2094_);
lean_inc(v_v_2093_);
lean_inc(v_k_2092_);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_l_2078_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2128_ = lean_ctor_get(v_l_2078_, 4);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_l_2078_, 3);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_l_2078_, 2);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_l_2078_, 1);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_2078_, 0);
lean_dec(v_unused_2132_);
v___x_2101_ = v_l_2078_;
v_isShared_2102_ = v_isSharedCheck_2127_;
goto v_resetjp_2100_;
}
else
{
lean_dec(v_l_2078_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2127_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2117_; 
v___x_2103_ = lean_nat_add(v___x_2073_, v_size_2074_);
v___x_2104_ = lean_nat_add(v___x_2103_, v_size_2075_);
lean_dec(v_size_2075_);
if (lean_obj_tag(v_l_2094_) == 0)
{
lean_object* v_size_2125_; 
v_size_2125_ = lean_ctor_get(v_l_2094_, 0);
lean_inc(v_size_2125_);
v___y_2117_ = v_size_2125_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___y_2117_ = v___x_2126_;
goto v___jp_2116_;
}
v___jp_2105_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_nat_add(v___y_2106_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec(v___y_2106_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_r_2079_);
lean_ctor_set(v___x_2101_, 3, v_r_2095_);
lean_ctor_set(v___x_2101_, 2, v_v_2077_);
lean_ctor_set(v___x_2101_, 1, v_k_2076_);
lean_ctor_set(v___x_2101_, 0, v___x_2109_);
v___x_2111_ = v___x_2101_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_k_2076_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_v_2077_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_r_2095_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_r_2079_);
v___x_2111_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2113_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v___x_2111_);
lean_ctor_set(v___x_2089_, 3, v___y_2107_);
lean_ctor_set(v___x_2089_, 2, v_v_2093_);
lean_ctor_set(v___x_2089_, 1, v_k_2092_);
lean_ctor_set(v___x_2089_, 0, v___x_2104_);
v___x_2113_ = v___x_2089_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v___y_2107_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
v___jp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_nat_add(v___x_2103_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec(v___x_2103_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_l_2094_);
lean_ctor_set(v___x_2068_, 0, v___x_2118_);
v___x_2120_ = v___x_2068_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_l_2065_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_l_2094_);
v___x_2120_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_nat_add(v___x_2073_, v_size_2096_);
if (lean_obj_tag(v_r_2095_) == 0)
{
lean_object* v_size_2122_; 
v_size_2122_ = lean_ctor_get(v_r_2095_, 0);
lean_inc(v_size_2122_);
v___y_2106_ = v___x_2121_;
v___y_2107_ = v___x_2120_;
v___y_2108_ = v_size_2122_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___y_2106_ = v___x_2121_;
v___y_2107_ = v___x_2120_;
v___y_2108_ = v___x_2123_;
goto v___jp_2105_;
}
}
}
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_del_object(v___x_2068_);
v___x_2133_ = lean_nat_add(v___x_2073_, v_size_2074_);
v___x_2134_ = lean_nat_add(v___x_2133_, v_size_2075_);
lean_dec(v_size_2075_);
v___x_2135_ = lean_nat_add(v___x_2133_, v_size_2091_);
lean_dec(v___x_2133_);
lean_inc_ref(v_l_2065_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_l_2078_);
lean_ctor_set(v___x_2089_, 3, v_l_2065_);
lean_ctor_set(v___x_2089_, 2, v_v_2064_);
lean_ctor_set(v___x_2089_, 1, v_k_2063_);
lean_ctor_set(v___x_2089_, 0, v___x_2135_);
v___x_2137_ = v___x_2089_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v_l_2065_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_l_2078_);
v___x_2137_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_isSharedCheck_2144_ = !lean_is_exclusive(v_l_2065_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; 
v_unused_2145_ = lean_ctor_get(v_l_2065_, 4);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_l_2065_, 3);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_l_2065_, 2);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2065_, 1);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2065_, 0);
lean_dec(v_unused_2149_);
v___x_2139_ = v_l_2065_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v_l_2065_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 4, v_r_2079_);
lean_ctor_set(v___x_2139_, 3, v___x_2137_);
lean_ctor_set(v___x_2139_, 2, v_v_2077_);
lean_ctor_set(v___x_2139_, 1, v_k_2076_);
lean_ctor_set(v___x_2139_, 0, v___x_2134_);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_k_2076_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_v_2077_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_r_2079_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2157_; 
v_l_2157_ = lean_ctor_get(v_impl_2072_, 3);
lean_inc(v_l_2157_);
if (lean_obj_tag(v_l_2157_) == 0)
{
lean_object* v_r_2158_; lean_object* v_k_2159_; lean_object* v_v_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2183_; 
v_r_2158_ = lean_ctor_get(v_impl_2072_, 4);
v_k_2159_ = lean_ctor_get(v_impl_2072_, 1);
v_v_2160_ = lean_ctor_get(v_impl_2072_, 2);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_impl_2072_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2184_ = lean_ctor_get(v_impl_2072_, 3);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_impl_2072_, 0);
lean_dec(v_unused_2185_);
v___x_2162_ = v_impl_2072_;
v_isShared_2163_ = v_isSharedCheck_2183_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_r_2158_);
lean_inc(v_v_2160_);
lean_inc(v_k_2159_);
lean_dec(v_impl_2072_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2183_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_k_2164_; lean_object* v_v_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2179_; 
v_k_2164_ = lean_ctor_get(v_l_2157_, 1);
v_v_2165_ = lean_ctor_get(v_l_2157_, 2);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_l_2157_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; lean_object* v_unused_2181_; lean_object* v_unused_2182_; 
v_unused_2180_ = lean_ctor_get(v_l_2157_, 4);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_l_2157_, 3);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_l_2157_, 0);
lean_dec(v_unused_2182_);
v___x_2167_ = v_l_2157_;
v_isShared_2168_ = v_isSharedCheck_2179_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_v_2165_);
lean_inc(v_k_2164_);
lean_dec(v_l_2157_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2179_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2158_, 2);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 4, v_r_2158_);
lean_ctor_set(v___x_2167_, 3, v_r_2158_);
lean_ctor_set(v___x_2167_, 2, v_v_2064_);
lean_ctor_set(v___x_2167_, 1, v_k_2063_);
lean_ctor_set(v___x_2167_, 0, v___x_2073_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_r_2158_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_r_2158_);
v___x_2171_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
lean_inc(v_r_2158_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 3, v_r_2158_);
lean_ctor_set(v___x_2162_, 0, v___x_2073_);
v___x_2173_ = v___x_2162_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_2159_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_2160_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_r_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_r_2158_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v___x_2173_);
lean_ctor_set(v___x_2068_, 3, v___x_2171_);
lean_ctor_set(v___x_2068_, 2, v_v_2165_);
lean_ctor_set(v___x_2068_, 1, v_k_2164_);
lean_ctor_set(v___x_2068_, 0, v___x_2169_);
v___x_2175_ = v___x_2068_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_k_2164_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_v_2165_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
else
{
lean_object* v_r_2186_; 
v_r_2186_ = lean_ctor_get(v_impl_2072_, 4);
lean_inc(v_r_2186_);
if (lean_obj_tag(v_r_2186_) == 0)
{
lean_object* v_k_2187_; lean_object* v_v_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2199_; 
v_k_2187_ = lean_ctor_get(v_impl_2072_, 1);
v_v_2188_ = lean_ctor_get(v_impl_2072_, 2);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_impl_2072_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; lean_object* v_unused_2201_; lean_object* v_unused_2202_; 
v_unused_2200_ = lean_ctor_get(v_impl_2072_, 4);
lean_dec(v_unused_2200_);
v_unused_2201_ = lean_ctor_get(v_impl_2072_, 3);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_impl_2072_, 0);
lean_dec(v_unused_2202_);
v___x_2190_ = v_impl_2072_;
v_isShared_2191_ = v_isSharedCheck_2199_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_v_2188_);
lean_inc(v_k_2187_);
lean_dec(v_impl_2072_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2199_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = lean_unsigned_to_nat(3u);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 4, v_l_2157_);
lean_ctor_set(v___x_2190_, 2, v_v_2064_);
lean_ctor_set(v___x_2190_, 1, v_k_2063_);
lean_ctor_set(v___x_2190_, 0, v___x_2073_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_l_2157_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_l_2157_);
v___x_2194_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2196_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_r_2186_);
lean_ctor_set(v___x_2068_, 3, v___x_2194_);
lean_ctor_set(v___x_2068_, 2, v_v_2188_);
lean_ctor_set(v___x_2068_, 1, v_k_2187_);
lean_ctor_set(v___x_2068_, 0, v___x_2192_);
v___x_2196_ = v___x_2068_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_k_2187_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_v_2188_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v_r_2186_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_unsigned_to_nat(2u);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_impl_2072_);
lean_ctor_set(v___x_2068_, 3, v_r_2186_);
lean_ctor_set(v___x_2068_, 0, v___x_2203_);
v___x_2205_ = v___x_2068_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_r_2186_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_impl_2072_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
else
{
lean_object* v___x_2208_; 
lean_dec(v_v_2064_);
lean_dec(v_k_2063_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 2, v_v_2060_);
lean_ctor_set(v___x_2068_, 1, v_k_2059_);
v___x_2208_ = v___x_2068_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_size_2062_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_2059_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_2060_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_l_2065_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_r_2066_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v_impl_2210_; lean_object* v___x_2211_; 
lean_dec(v_size_2062_);
v_impl_2210_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2059_, v_v_2060_, v_l_2065_);
v___x_2211_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2066_) == 0)
{
lean_object* v_size_2212_; lean_object* v_size_2213_; lean_object* v_k_2214_; lean_object* v_v_2215_; lean_object* v_l_2216_; lean_object* v_r_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v_size_2212_ = lean_ctor_get(v_r_2066_, 0);
v_size_2213_ = lean_ctor_get(v_impl_2210_, 0);
lean_inc(v_size_2213_);
v_k_2214_ = lean_ctor_get(v_impl_2210_, 1);
lean_inc(v_k_2214_);
v_v_2215_ = lean_ctor_get(v_impl_2210_, 2);
lean_inc(v_v_2215_);
v_l_2216_ = lean_ctor_get(v_impl_2210_, 3);
lean_inc(v_l_2216_);
v_r_2217_ = lean_ctor_get(v_impl_2210_, 4);
lean_inc(v_r_2217_);
v___x_2218_ = lean_unsigned_to_nat(3u);
v___x_2219_ = lean_nat_mul(v___x_2218_, v_size_2212_);
v___x_2220_ = lean_nat_dec_lt(v___x_2219_, v_size_2213_);
lean_dec(v___x_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
lean_dec(v_r_2217_);
lean_dec(v_l_2216_);
lean_dec(v_v_2215_);
lean_dec(v_k_2214_);
v___x_2221_ = lean_nat_add(v___x_2211_, v_size_2213_);
lean_dec(v_size_2213_);
v___x_2222_ = lean_nat_add(v___x_2221_, v_size_2212_);
lean_dec(v___x_2221_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 3, v_impl_2210_);
lean_ctor_set(v___x_2068_, 0, v___x_2222_);
v___x_2224_ = v___x_2068_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_impl_2210_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_r_2066_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
else
{
lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2291_; 
v_isSharedCheck_2291_ = !lean_is_exclusive(v_impl_2210_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; lean_object* v_unused_2293_; lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2292_ = lean_ctor_get(v_impl_2210_, 4);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_impl_2210_, 3);
lean_dec(v_unused_2293_);
v_unused_2294_ = lean_ctor_get(v_impl_2210_, 2);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_impl_2210_, 1);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_impl_2210_, 0);
lean_dec(v_unused_2296_);
v___x_2227_ = v_impl_2210_;
v_isShared_2228_ = v_isSharedCheck_2291_;
goto v_resetjp_2226_;
}
else
{
lean_dec(v_impl_2210_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2291_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_size_2229_; lean_object* v_size_2230_; lean_object* v_k_2231_; lean_object* v_v_2232_; lean_object* v_l_2233_; lean_object* v_r_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_size_2229_ = lean_ctor_get(v_l_2216_, 0);
v_size_2230_ = lean_ctor_get(v_r_2217_, 0);
v_k_2231_ = lean_ctor_get(v_r_2217_, 1);
v_v_2232_ = lean_ctor_get(v_r_2217_, 2);
v_l_2233_ = lean_ctor_get(v_r_2217_, 3);
v_r_2234_ = lean_ctor_get(v_r_2217_, 4);
v___x_2235_ = lean_unsigned_to_nat(2u);
v___x_2236_ = lean_nat_mul(v___x_2235_, v_size_2229_);
v___x_2237_ = lean_nat_dec_lt(v_size_2230_, v___x_2236_);
lean_dec(v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2266_; 
lean_inc(v_r_2234_);
lean_inc(v_l_2233_);
lean_inc(v_v_2232_);
lean_inc(v_k_2231_);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_r_2217_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; lean_object* v_unused_2268_; lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; 
v_unused_2267_ = lean_ctor_get(v_r_2217_, 4);
lean_dec(v_unused_2267_);
v_unused_2268_ = lean_ctor_get(v_r_2217_, 3);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_r_2217_, 2);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_r_2217_, 1);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_r_2217_, 0);
lean_dec(v_unused_2271_);
v___x_2239_ = v_r_2217_;
v_isShared_2240_ = v_isSharedCheck_2266_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v_r_2217_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2266_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___x_2254_; lean_object* v___y_2256_; 
v___x_2241_ = lean_nat_add(v___x_2211_, v_size_2213_);
lean_dec(v_size_2213_);
v___x_2242_ = lean_nat_add(v___x_2241_, v_size_2212_);
lean_dec(v___x_2241_);
v___x_2254_ = lean_nat_add(v___x_2211_, v_size_2229_);
if (lean_obj_tag(v_l_2233_) == 0)
{
lean_object* v_size_2264_; 
v_size_2264_ = lean_ctor_get(v_l_2233_, 0);
lean_inc(v_size_2264_);
v___y_2256_ = v_size_2264_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___y_2256_ = v___x_2265_;
goto v___jp_2255_;
}
v___jp_2243_:
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2247_ = lean_nat_add(v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec(v___y_2245_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 4, v_r_2066_);
lean_ctor_set(v___x_2239_, 3, v_r_2234_);
lean_ctor_set(v___x_2239_, 2, v_v_2064_);
lean_ctor_set(v___x_2239_, 1, v_k_2063_);
lean_ctor_set(v___x_2239_, 0, v___x_2247_);
v___x_2249_ = v___x_2239_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_r_2234_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_r_2066_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 4, v___x_2249_);
lean_ctor_set(v___x_2227_, 3, v___y_2244_);
lean_ctor_set(v___x_2227_, 2, v_v_2232_);
lean_ctor_set(v___x_2227_, 1, v_k_2231_);
lean_ctor_set(v___x_2227_, 0, v___x_2242_);
v___x_2251_ = v___x_2227_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2231_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2232_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v___y_2244_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_nat_add(v___x_2254_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec(v___x_2254_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_l_2233_);
lean_ctor_set(v___x_2068_, 3, v_l_2216_);
lean_ctor_set(v___x_2068_, 2, v_v_2215_);
lean_ctor_set(v___x_2068_, 1, v_k_2214_);
lean_ctor_set(v___x_2068_, 0, v___x_2257_);
v___x_2259_ = v___x_2068_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_k_2214_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_v_2215_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_l_2216_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_l_2233_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_nat_add(v___x_2211_, v_size_2212_);
if (lean_obj_tag(v_r_2234_) == 0)
{
lean_object* v_size_2261_; 
v_size_2261_ = lean_ctor_get(v_r_2234_, 0);
lean_inc(v_size_2261_);
v___y_2244_ = v___x_2259_;
v___y_2245_ = v___x_2260_;
v___y_2246_ = v_size_2261_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2262_; 
v___x_2262_ = lean_unsigned_to_nat(0u);
v___y_2244_ = v___x_2259_;
v___y_2245_ = v___x_2260_;
v___y_2246_ = v___x_2262_;
goto v___jp_2243_;
}
}
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_del_object(v___x_2068_);
v___x_2272_ = lean_nat_add(v___x_2211_, v_size_2213_);
lean_dec(v_size_2213_);
v___x_2273_ = lean_nat_add(v___x_2272_, v_size_2212_);
lean_dec(v___x_2272_);
v___x_2274_ = lean_nat_add(v___x_2211_, v_size_2212_);
v___x_2275_ = lean_nat_add(v___x_2274_, v_size_2230_);
lean_dec(v___x_2274_);
lean_inc_ref(v_r_2066_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 4, v_r_2066_);
lean_ctor_set(v___x_2227_, 3, v_r_2217_);
lean_ctor_set(v___x_2227_, 2, v_v_2064_);
lean_ctor_set(v___x_2227_, 1, v_k_2063_);
lean_ctor_set(v___x_2227_, 0, v___x_2275_);
v___x_2277_ = v___x_2227_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_r_2217_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v_r_2066_);
v___x_2277_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_isSharedCheck_2284_ = !lean_is_exclusive(v_r_2066_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; lean_object* v_unused_2286_; lean_object* v_unused_2287_; lean_object* v_unused_2288_; lean_object* v_unused_2289_; 
v_unused_2285_ = lean_ctor_get(v_r_2066_, 4);
lean_dec(v_unused_2285_);
v_unused_2286_ = lean_ctor_get(v_r_2066_, 3);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_r_2066_, 2);
lean_dec(v_unused_2287_);
v_unused_2288_ = lean_ctor_get(v_r_2066_, 1);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_r_2066_, 0);
lean_dec(v_unused_2289_);
v___x_2279_ = v_r_2066_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_dec(v_r_2066_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 4, v___x_2277_);
lean_ctor_set(v___x_2279_, 3, v_l_2216_);
lean_ctor_set(v___x_2279_, 2, v_v_2215_);
lean_ctor_set(v___x_2279_, 1, v_k_2214_);
lean_ctor_set(v___x_2279_, 0, v___x_2273_);
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_k_2214_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_v_2215_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v_l_2216_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v___x_2277_);
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
}
}
else
{
lean_object* v_l_2297_; 
v_l_2297_ = lean_ctor_get(v_impl_2210_, 3);
lean_inc(v_l_2297_);
if (lean_obj_tag(v_l_2297_) == 0)
{
lean_object* v_r_2298_; lean_object* v_k_2299_; lean_object* v_v_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2311_; 
v_r_2298_ = lean_ctor_get(v_impl_2210_, 4);
v_k_2299_ = lean_ctor_get(v_impl_2210_, 1);
v_v_2300_ = lean_ctor_get(v_impl_2210_, 2);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_impl_2210_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; lean_object* v_unused_2313_; 
v_unused_2312_ = lean_ctor_get(v_impl_2210_, 3);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_impl_2210_, 0);
lean_dec(v_unused_2313_);
v___x_2302_ = v_impl_2210_;
v_isShared_2303_ = v_isSharedCheck_2311_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_r_2298_);
lean_inc(v_v_2300_);
lean_inc(v_k_2299_);
lean_dec(v_impl_2210_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2311_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2298_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 3, v_r_2298_);
lean_ctor_set(v___x_2302_, 2, v_v_2064_);
lean_ctor_set(v___x_2302_, 1, v_k_2063_);
lean_ctor_set(v___x_2302_, 0, v___x_2211_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_r_2298_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v_r_2298_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v___x_2306_);
lean_ctor_set(v___x_2068_, 3, v_l_2297_);
lean_ctor_set(v___x_2068_, 2, v_v_2300_);
lean_ctor_set(v___x_2068_, 1, v_k_2299_);
lean_ctor_set(v___x_2068_, 0, v___x_2304_);
v___x_2308_ = v___x_2068_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2299_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2300_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_l_2297_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_r_2314_; 
v_r_2314_ = lean_ctor_get(v_impl_2210_, 4);
lean_inc(v_r_2314_);
if (lean_obj_tag(v_r_2314_) == 0)
{
lean_object* v_k_2315_; lean_object* v_v_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2339_; 
v_k_2315_ = lean_ctor_get(v_impl_2210_, 1);
v_v_2316_ = lean_ctor_get(v_impl_2210_, 2);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_impl_2210_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; lean_object* v_unused_2341_; lean_object* v_unused_2342_; 
v_unused_2340_ = lean_ctor_get(v_impl_2210_, 4);
lean_dec(v_unused_2340_);
v_unused_2341_ = lean_ctor_get(v_impl_2210_, 3);
lean_dec(v_unused_2341_);
v_unused_2342_ = lean_ctor_get(v_impl_2210_, 0);
lean_dec(v_unused_2342_);
v___x_2318_ = v_impl_2210_;
v_isShared_2319_ = v_isSharedCheck_2339_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_v_2316_);
lean_inc(v_k_2315_);
lean_dec(v_impl_2210_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2339_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_k_2320_; lean_object* v_v_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2335_; 
v_k_2320_ = lean_ctor_get(v_r_2314_, 1);
v_v_2321_ = lean_ctor_get(v_r_2314_, 2);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_r_2314_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; lean_object* v_unused_2337_; lean_object* v_unused_2338_; 
v_unused_2336_ = lean_ctor_get(v_r_2314_, 4);
lean_dec(v_unused_2336_);
v_unused_2337_ = lean_ctor_get(v_r_2314_, 3);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_r_2314_, 0);
lean_dec(v_unused_2338_);
v___x_2323_ = v_r_2314_;
v_isShared_2324_ = v_isSharedCheck_2335_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_v_2321_);
lean_inc(v_k_2320_);
lean_dec(v_r_2314_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2335_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_unsigned_to_nat(3u);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_l_2297_);
lean_ctor_set(v___x_2323_, 3, v_l_2297_);
lean_ctor_set(v___x_2323_, 2, v_v_2316_);
lean_ctor_set(v___x_2323_, 1, v_k_2315_);
lean_ctor_set(v___x_2323_, 0, v___x_2211_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_k_2315_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_v_2316_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_l_2297_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_l_2297_);
v___x_2327_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 4, v_l_2297_);
lean_ctor_set(v___x_2318_, 2, v_v_2064_);
lean_ctor_set(v___x_2318_, 1, v_k_2063_);
lean_ctor_set(v___x_2318_, 0, v___x_2211_);
v___x_2329_ = v___x_2318_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_l_2297_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_l_2297_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v___x_2329_);
lean_ctor_set(v___x_2068_, 3, v___x_2327_);
lean_ctor_set(v___x_2068_, 2, v_v_2321_);
lean_ctor_set(v___x_2068_, 1, v_k_2320_);
lean_ctor_set(v___x_2068_, 0, v___x_2325_);
v___x_2331_ = v___x_2068_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_k_2320_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_v_2321_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2343_ = lean_unsigned_to_nat(2u);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_r_2314_);
lean_ctor_set(v___x_2068_, 3, v_impl_2210_);
lean_ctor_set(v___x_2068_, 0, v___x_2343_);
v___x_2345_ = v___x_2068_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_impl_2210_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_r_2314_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
lean_ctor_set(v___x_2349_, 1, v_k_2059_);
lean_ctor_set(v___x_2349_, 2, v_v_2060_);
lean_ctor_set(v___x_2349_, 3, v_t_2061_);
lean_ctor_set(v___x_2349_, 4, v_t_2061_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(lean_object* v_k_2350_, lean_object* v_v_2351_, lean_object* v_x_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v_a_2361_; lean_object* v_optionsPerPos_2362_; lean_object* v_currNamespace_2363_; lean_object* v_openDecls_2364_; uint8_t v_inPattern_2365_; lean_object* v_subExpr_2366_; lean_object* v_depth_2367_; lean_object* v_lctxInitIndices_2368_; lean_object* v___y_2370_; lean_object* v___x_2375_; 
v___x_2360_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2353_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2360_);
v_optionsPerPos_2362_ = lean_ctor_get(v_a_2353_, 0);
v_currNamespace_2363_ = lean_ctor_get(v_a_2353_, 1);
v_openDecls_2364_ = lean_ctor_get(v_a_2353_, 2);
v_inPattern_2365_ = lean_ctor_get_uint8(v_a_2353_, sizeof(void*)*6);
v_subExpr_2366_ = lean_ctor_get(v_a_2353_, 3);
v_depth_2367_ = lean_ctor_get(v_a_2353_, 4);
v_lctxInitIndices_2368_ = lean_ctor_get(v_a_2353_, 5);
v___x_2375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__2___redArg(v_optionsPerPos_2362_, v_a_2361_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Options_empty;
v___y_2370_ = v___x_2376_;
goto v___jp_2369_;
}
else
{
lean_object* v_val_2377_; 
v_val_2377_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_val_2377_);
lean_dec_ref_known(v___x_2375_, 1);
v___y_2370_ = v_val_2377_;
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2371_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__0(v___y_2370_, v_k_2350_, v_v_2351_);
lean_inc(v_optionsPerPos_2362_);
v___x_2372_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_a_2361_, v___x_2371_, v_optionsPerPos_2362_);
lean_inc(v_lctxInitIndices_2368_);
lean_inc(v_depth_2367_);
lean_inc_ref(v_subExpr_2366_);
lean_inc(v_openDecls_2364_);
lean_inc(v_currNamespace_2363_);
v___x_2373_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v_currNamespace_2363_);
lean_ctor_set(v___x_2373_, 2, v_openDecls_2364_);
lean_ctor_set(v___x_2373_, 3, v_subExpr_2366_);
lean_ctor_set(v___x_2373_, 4, v_depth_2367_);
lean_ctor_set(v___x_2373_, 5, v_lctxInitIndices_2368_);
lean_ctor_set_uint8(v___x_2373_, sizeof(void*)*6, v_inPattern_2365_);
lean_inc(v_a_2358_);
lean_inc_ref(v_a_2357_);
lean_inc(v_a_2356_);
lean_inc_ref(v_a_2355_);
lean_inc(v_a_2354_);
v___x_2374_ = lean_apply_7(v_x_2352_, v___x_2373_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, lean_box(0));
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg___boxed(lean_object* v_k_2378_, lean_object* v_v_2379_, lean_object* v_x_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2378_, v_v_2379_, v_x_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* v_00_u03b1_2389_, lean_object* v_k_2390_, lean_object* v_v_2391_, lean_object* v_x_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___redArg(v_k_2390_, v_v_2391_, v_x_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_k_2402_, lean_object* v_v_2403_, lean_object* v_x_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(v_00_u03b1_2401_, v_k_2402_, v_v_2403_, v_x_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0(lean_object* v_00_u03b2_2413_, lean_object* v_k_2414_, lean_object* v_v_2415_, lean_object* v_t_2416_, lean_object* v_hl_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_k_2414_, v_v_2415_, v_t_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* v_pos_2419_, lean_object* v_stx_2420_){
_start:
{
uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2421_ = 0;
lean_inc(v_pos_2419_);
v___x_2422_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2422_, 0, v_pos_2419_);
lean_ctor_set(v___x_2422_, 1, v_pos_2419_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*2, v___x_2421_);
v___x_2423_ = l_Lean_Syntax_setInfo(v___x_2422_, v_stx_2420_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(lean_object* v_stx_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2436_; 
v___x_2427_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2425_);
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2432_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_2428_, v_stx_2424_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2432_);
v___x_2434_ = v___x_2430_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg___boxed(lean_object* v_stx_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2437_, v_a_2438_);
lean_dec_ref(v_a_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* v_stx_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2441_, v_a_2442_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* v_stx_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(v_stx_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(lean_object* v_stx_2461_, lean_object* v_e_2462_, uint8_t v_isBinder_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_lctx_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v_lctx_2466_ = lean_ctor_get(v_a_2464_, 2);
v___x_2467_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___closed__0));
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v_stx_2461_);
v___x_2469_ = lean_box(0);
v___x_2470_ = 0;
lean_inc_ref(v_lctx_2466_);
v___x_2471_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2471_, 0, v___x_2468_);
lean_ctor_set(v___x_2471_, 1, v_lctx_2466_);
lean_ctor_set(v___x_2471_, 2, v___x_2469_);
lean_ctor_set(v___x_2471_, 3, v_e_2462_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*4, v_isBinder_2463_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*4 + 1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg___boxed(lean_object* v_stx_2473_, lean_object* v_e_2474_, lean_object* v_isBinder_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
uint8_t v_isBinder_boxed_2478_; lean_object* v_res_2479_; 
v_isBinder_boxed_2478_ = lean_unbox(v_isBinder_2475_);
v_res_2479_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2473_, v_e_2474_, v_isBinder_boxed_2478_, v_a_2476_);
lean_dec_ref(v_a_2476_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* v_stx_2480_, lean_object* v_e_2481_, uint8_t v_isBinder_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2480_, v_e_2481_, v_isBinder_2482_, v_a_2485_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* v_stx_2491_, lean_object* v_e_2492_, lean_object* v_isBinder_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
uint8_t v_isBinder_boxed_2501_; lean_object* v_res_2502_; 
v_isBinder_boxed_2501_ = lean_unbox(v_isBinder_2493_);
v_res_2502_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(v_stx_2491_, v_e_2492_, v_isBinder_boxed_2501_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(lean_object* v_pos_2503_, lean_object* v_stx_2504_, lean_object* v_e_2505_, uint8_t v_isBinder_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2533_; 
v___x_2510_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2504_, v_e_2505_, v_isBinder_2506_, v_a_2508_);
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2533_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2533_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v_steps_2516_; lean_object* v_infos_2517_; lean_object* v_holeIter_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2532_; 
v___x_2515_ = lean_st_ref_take(v_a_2507_);
v_steps_2516_ = lean_ctor_get(v___x_2515_, 0);
v_infos_2517_ = lean_ctor_get(v___x_2515_, 1);
v_holeIter_2518_ = lean_ctor_get(v___x_2515_, 2);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2520_ = v___x_2515_;
v_isShared_2521_ = v_isSharedCheck_2532_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_holeIter_2518_);
lean_inc(v_infos_2517_);
lean_inc(v_steps_2516_);
lean_dec(v___x_2515_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2532_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_a_2511_);
v___x_2523_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2503_, v___x_2522_, v_infos_2517_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 1, v___x_2523_);
v___x_2525_ = v___x_2520_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_steps_2516_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_holeIter_2518_);
v___x_2525_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = lean_st_ref_put(v_a_2507_, v___x_2525_);
v___x_2527_ = lean_box(0);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2527_);
v___x_2529_ = v___x_2513_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg___boxed(lean_object* v_pos_2534_, lean_object* v_stx_2535_, lean_object* v_e_2536_, lean_object* v_isBinder_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
uint8_t v_isBinder_boxed_2541_; lean_object* v_res_2542_; 
v_isBinder_boxed_2541_ = lean_unbox(v_isBinder_2537_);
v_res_2542_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2534_, v_stx_2535_, v_e_2536_, v_isBinder_boxed_2541_, v_a_2538_, v_a_2539_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* v_pos_2543_, lean_object* v_stx_2544_, lean_object* v_e_2545_, uint8_t v_isBinder_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_pos_2543_, v_stx_2544_, v_e_2545_, v_isBinder_2546_, v_a_2548_, v_a_2549_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* v_pos_2555_, lean_object* v_stx_2556_, lean_object* v_e_2557_, lean_object* v_isBinder_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
uint8_t v_isBinder_boxed_2566_; lean_object* v_res_2567_; 
v_isBinder_boxed_2566_ = lean_unbox(v_isBinder_2558_);
v_res_2567_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo(v_pos_2555_, v_stx_2556_, v_e_2557_, v_isBinder_boxed_2566_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(lean_object* v_projName_2568_, lean_object* v_fieldName_2569_, lean_object* v_stx_2570_, lean_object* v_val_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_lctx_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_lctx_2574_ = lean_ctor_get(v_a_2572_, 2);
lean_inc_ref(v_lctx_2574_);
v___x_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2575_, 0, v_projName_2568_);
lean_ctor_set(v___x_2575_, 1, v_fieldName_2569_);
lean_ctor_set(v___x_2575_, 2, v_lctx_2574_);
lean_ctor_set(v___x_2575_, 3, v_val_2571_);
lean_ctor_set(v___x_2575_, 4, v_stx_2570_);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg___boxed(lean_object* v_projName_2577_, lean_object* v_fieldName_2578_, lean_object* v_stx_2579_, lean_object* v_val_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2577_, v_fieldName_2578_, v_stx_2579_, v_val_2580_, v_a_2581_);
lean_dec_ref(v_a_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* v_projName_2584_, lean_object* v_fieldName_2585_, lean_object* v_stx_2586_, lean_object* v_val_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2584_, v_fieldName_2585_, v_stx_2586_, v_val_2587_, v_a_2590_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* v_projName_2596_, lean_object* v_fieldName_2597_, lean_object* v_stx_2598_, lean_object* v_val_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(v_projName_2596_, v_fieldName_2597_, v_stx_2598_, v_val_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(lean_object* v_pos_2608_, lean_object* v_projName_2609_, lean_object* v_fieldName_2610_, lean_object* v_stx_2611_, lean_object* v_val_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___x_2616_; lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2639_; 
v___x_2616_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___redArg(v_projName_2609_, v_fieldName_2610_, v_stx_2611_, v_val_2612_, v_a_2614_);
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2639_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2639_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v_steps_2622_; lean_object* v_infos_2623_; lean_object* v_holeIter_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2638_; 
v___x_2621_ = lean_st_ref_take(v_a_2613_);
v_steps_2622_ = lean_ctor_get(v___x_2621_, 0);
v_infos_2623_ = lean_ctor_get(v___x_2621_, 1);
v_holeIter_2624_ = lean_ctor_get(v___x_2621_, 2);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2626_ = v___x_2621_;
v_isShared_2627_ = v_isSharedCheck_2638_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_holeIter_2624_);
lean_inc(v_infos_2623_);
lean_inc(v_steps_2622_);
lean_dec(v___x_2621_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2638_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2628_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_a_2617_);
v___x_2629_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2608_, v___x_2628_, v_infos_2623_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 1, v___x_2629_);
v___x_2631_ = v___x_2626_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_steps_2622_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_holeIter_2624_);
v___x_2631_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2632_ = lean_st_ref_put(v_a_2613_, v___x_2631_);
v___x_2633_ = lean_box(0);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2633_);
v___x_2635_ = v___x_2619_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg___boxed(lean_object* v_pos_2640_, lean_object* v_projName_2641_, lean_object* v_fieldName_2642_, lean_object* v_stx_2643_, lean_object* v_val_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2640_, v_projName_2641_, v_fieldName_2642_, v_stx_2643_, v_val_2644_, v_a_2645_, v_a_2646_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* v_pos_2649_, lean_object* v_projName_2650_, lean_object* v_fieldName_2651_, lean_object* v_stx_2652_, lean_object* v_val_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo___redArg(v_pos_2649_, v_projName_2650_, v_fieldName_2651_, v_stx_2652_, v_val_2653_, v_a_2655_, v_a_2656_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* v_pos_2662_, lean_object* v_projName_2663_, lean_object* v_fieldName_2664_, lean_object* v_stx_2665_, lean_object* v_val_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(v_pos_2662_, v_projName_2663_, v_fieldName_2664_, v_stx_2665_, v_val_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(lean_object* v_val_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_val_2675_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed(lean_object* v_val_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0(v_val_2679_, v___y_2680_);
lean_dec_ref(v___y_2680_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(lean_object* v_pos_2683_, lean_object* v_stx_2684_, lean_object* v_e_2685_, uint8_t v_isBinder_2686_, lean_object* v_location_x3f_2687_, lean_object* v_docString_x3f_2688_, lean_object* v_mkDocString_x3f_2689_, uint8_t v_explicit_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v___x_2694_; lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2729_; 
v___x_2694_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___redArg(v_stx_2684_, v_e_2685_, v_isBinder_2686_, v_a_2692_);
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2729_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2729_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___y_2700_; 
if (lean_obj_tag(v_mkDocString_x3f_2689_) == 0)
{
if (lean_obj_tag(v_docString_x3f_2688_) == 0)
{
v___y_2700_ = v_mkDocString_x3f_2689_;
goto v___jp_2699_;
}
else
{
lean_object* v_val_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2728_; 
v_val_2720_ = lean_ctor_get(v_docString_x3f_2688_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_docString_x3f_2688_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2722_ = v_docString_x3f_2688_;
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_val_2720_);
lean_dec(v_docString_x3f_2688_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___f_2724_; lean_object* v___x_2726_; 
v___f_2724_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2724_, 0, v_val_2720_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___f_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___f_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
v___y_2700_ = v___x_2726_;
goto v___jp_2699_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_2688_);
v___y_2700_ = v_mkDocString_x3f_2689_;
goto v___jp_2699_;
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v_steps_2702_; lean_object* v_infos_2703_; lean_object* v_holeIter_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2719_; 
v___x_2701_ = lean_st_ref_take(v_a_2691_);
v_steps_2702_ = lean_ctor_get(v___x_2701_, 0);
v_infos_2703_ = lean_ctor_get(v___x_2701_, 1);
v_holeIter_2704_ = lean_ctor_get(v___x_2701_, 2);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2706_ = v___x_2701_;
v_isShared_2707_ = v_isSharedCheck_2719_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_holeIter_2704_);
lean_inc(v_infos_2703_);
lean_inc(v_steps_2702_);
lean_dec(v___x_2701_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2719_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2708_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2708_, 0, v_a_2695_);
lean_ctor_set(v___x_2708_, 1, v_location_x3f_2687_);
lean_ctor_set(v___x_2708_, 2, v___y_2700_);
lean_ctor_set_uint8(v___x_2708_, sizeof(void*)*3, v_explicit_2690_);
v___x_2709_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos_spec__0___redArg(v_pos_2683_, v___x_2709_, v_infos_2703_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 1, v___x_2710_);
v___x_2712_ = v___x_2706_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_steps_2702_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_holeIter_2704_);
v___x_2712_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2713_ = lean_st_ref_put(v_a_2691_, v___x_2712_);
v___x_2714_ = lean_box(0);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2714_);
v___x_2716_ = v___x_2697_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg___boxed(lean_object* v_pos_2730_, lean_object* v_stx_2731_, lean_object* v_e_2732_, lean_object* v_isBinder_2733_, lean_object* v_location_x3f_2734_, lean_object* v_docString_x3f_2735_, lean_object* v_mkDocString_x3f_2736_, lean_object* v_explicit_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
uint8_t v_isBinder_boxed_2741_; uint8_t v_explicit_boxed_2742_; lean_object* v_res_2743_; 
v_isBinder_boxed_2741_ = lean_unbox(v_isBinder_2733_);
v_explicit_boxed_2742_ = lean_unbox(v_explicit_2737_);
v_res_2743_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2730_, v_stx_2731_, v_e_2732_, v_isBinder_boxed_2741_, v_location_x3f_2734_, v_docString_x3f_2735_, v_mkDocString_x3f_2736_, v_explicit_boxed_2742_, v_a_2738_, v_a_2739_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(lean_object* v_pos_2744_, lean_object* v_stx_2745_, lean_object* v_e_2746_, uint8_t v_isBinder_2747_, lean_object* v_location_x3f_2748_, lean_object* v_docString_x3f_2749_, lean_object* v_mkDocString_x3f_2750_, uint8_t v_explicit_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_2744_, v_stx_2745_, v_e_2746_, v_isBinder_2747_, v_location_x3f_2748_, v_docString_x3f_2749_, v_mkDocString_x3f_2750_, v_explicit_2751_, v_a_2753_, v_a_2754_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___boxed(lean_object* v_pos_2760_, lean_object* v_stx_2761_, lean_object* v_e_2762_, lean_object* v_isBinder_2763_, lean_object* v_location_x3f_2764_, lean_object* v_docString_x3f_2765_, lean_object* v_mkDocString_x3f_2766_, lean_object* v_explicit_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
uint8_t v_isBinder_boxed_2775_; uint8_t v_explicit_boxed_2776_; lean_object* v_res_2777_; 
v_isBinder_boxed_2775_ = lean_unbox(v_isBinder_2763_);
v_explicit_boxed_2776_ = lean_unbox(v_explicit_2767_);
v_res_2777_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo(v_pos_2760_, v_stx_2761_, v_e_2762_, v_isBinder_boxed_2775_, v_location_x3f_2764_, v_docString_x3f_2765_, v_mkDocString_x3f_2766_, v_explicit_boxed_2776_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(lean_object* v_stx_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v_stx_2778_, v_a_2779_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v_a_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc_n(v_a_2784_, 2);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_2779_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_2779_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = 0;
v___x_2790_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_2786_, v_a_2784_, v_a_2788_, v___x_2789_, v_a_2780_, v_a_2781_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2790_, 0);
lean_dec(v_unused_2798_);
v___x_2792_ = v___x_2790_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_dec(v___x_2790_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v_a_2784_);
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2784_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2784_);
v_a_2799_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2790_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2790_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
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
else
{
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg___boxed(lean_object* v_stx_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(lean_object* v_stx_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___boxed(lean_object* v_stx_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo(v_stx_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
return v_res_2830_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(lean_object* v_k_2831_, lean_object* v_t_2832_){
_start:
{
if (lean_obj_tag(v_t_2832_) == 0)
{
lean_object* v_k_2833_; lean_object* v_l_2834_; lean_object* v_r_2835_; uint8_t v___x_2836_; 
v_k_2833_ = lean_ctor_get(v_t_2832_, 1);
v_l_2834_ = lean_ctor_get(v_t_2832_, 3);
v_r_2835_ = lean_ctor_get(v_t_2832_, 4);
v___x_2836_ = lean_nat_dec_lt(v_k_2831_, v_k_2833_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = lean_nat_dec_eq(v_k_2831_, v_k_2833_);
if (v___x_2837_ == 0)
{
v_t_2832_ = v_r_2835_;
goto _start;
}
else
{
return v___x_2837_;
}
}
else
{
v_t_2832_ = v_l_2834_;
goto _start;
}
}
else
{
uint8_t v___x_2840_; 
v___x_2840_ = 0;
return v___x_2840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg___boxed(lean_object* v_k_2841_, lean_object* v_t_2842_){
_start:
{
uint8_t v_res_2843_; lean_object* v_r_2844_; 
v_res_2843_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2841_, v_t_2842_);
lean_dec(v_t_2842_);
lean_dec(v_k_2841_);
v_r_2844_ = lean_box(v_res_2843_);
return v_r_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(lean_object* v_stx_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_Syntax_getInfo_x3f(v_stx_2845_);
if (lean_obj_tag(v___x_2850_) == 1)
{
lean_object* v_val_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2869_; 
v_val_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2869_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_val_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2869_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
if (lean_obj_tag(v_val_2851_) == 1)
{
uint8_t v_canonical_2855_; 
v_canonical_2855_ = lean_ctor_get_uint8(v_val_2851_, sizeof(void*)*2);
if (v_canonical_2855_ == 0)
{
lean_object* v_pos_2856_; lean_object* v_endPos_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_pos_2856_ = lean_ctor_get(v_val_2851_, 0);
lean_inc(v_pos_2856_);
v_endPos_2857_ = lean_ctor_get(v_val_2851_, 1);
lean_inc(v_endPos_2857_);
lean_dec_ref_known(v_val_2851_, 2);
v___x_2858_ = lean_st_ref_get(v_a_2847_);
v___x_2859_ = lean_nat_dec_eq(v_pos_2856_, v_endPos_2857_);
lean_dec(v_endPos_2857_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec(v___x_2858_);
lean_dec(v_pos_2856_);
lean_del_object(v___x_2853_);
v___x_2860_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2860_;
}
else
{
lean_object* v_infos_2861_; uint8_t v___x_2862_; 
v_infos_2861_ = lean_ctor_get(v___x_2858_, 1);
lean_inc(v_infos_2861_);
lean_dec(v___x_2858_);
v___x_2862_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_pos_2856_, v_infos_2861_);
lean_dec(v_infos_2861_);
lean_dec(v_pos_2856_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
lean_del_object(v___x_2853_);
v___x_2863_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2863_;
}
else
{
lean_object* v___x_2865_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 0);
lean_ctor_set(v___x_2853_, 0, v_stx_2845_);
v___x_2865_ = v___x_2853_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_stx_2845_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v___x_2867_; 
lean_dec_ref_known(v_val_2851_, 2);
lean_del_object(v___x_2853_);
v___x_2867_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2867_;
}
}
else
{
lean_object* v___x_2868_; 
lean_del_object(v___x_2853_);
lean_dec(v_val_2851_);
v___x_2868_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2868_;
}
}
}
else
{
lean_object* v___x_2870_; 
lean_dec(v___x_2850_);
v___x_2870_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_stx_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg___boxed(lean_object* v_stx_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(lean_object* v_stx_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_stx_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___boxed(lean_object* v_stx_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated(v_stx_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
return v_res_2894_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(lean_object* v_00_u03b2_2895_, lean_object* v_k_2896_, lean_object* v_t_2897_){
_start:
{
uint8_t v___x_2898_; 
v___x_2898_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___redArg(v_k_2896_, v_t_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0___boxed(lean_object* v_00_u03b2_2899_, lean_object* v_k_2900_, lean_object* v_t_2901_){
_start:
{
uint8_t v_res_2902_; lean_object* v_r_2903_; 
v_res_2902_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated_spec__0(v_00_u03b2_2899_, v_k_2900_, v_t_2901_);
lean_dec(v_t_2901_);
lean_dec(v_k_2900_);
v_r_2903_ = lean_box(v_res_2902_);
return v_r_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(lean_object* v_d_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v___x_2912_; 
lean_inc(v_a_2910_);
lean_inc_ref(v_a_2909_);
lean_inc(v_a_2908_);
lean_inc_ref(v_a_2907_);
lean_inc(v_a_2906_);
lean_inc_ref(v_a_2905_);
v___x_2912_ = lean_apply_7(v_d_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, lean_box(0));
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v___x_2914_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfo___redArg(v_a_2913_, v_a_2905_, v_a_2906_, v_a_2907_);
return v___x_2914_;
}
else
{
return v___x_2912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo___boxed(lean_object* v_d_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfo(v_d_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(lean_object* v_d_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v___x_2932_; 
lean_inc(v_a_2930_);
lean_inc_ref(v_a_2929_);
lean_inc(v_a_2928_);
lean_inc_ref(v_a_2927_);
lean_inc(v_a_2926_);
lean_inc_ref(v_a_2925_);
v___x_2932_ = lean_apply_7(v_d_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, lean_box(0));
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_2933_, v_a_2925_, v_a_2926_, v_a_2927_);
return v___x_2934_;
}
else
{
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated___boxed(lean_object* v_d_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_PrettyPrinter_Delaborator_withAnnotateTermInfoUnlessAnnotated(v_d_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2943_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(lean_object* v_lctx_2944_, lean_object* v_suggestion_x27_2945_, lean_object* v_x_2946_){
_start:
{
if (lean_obj_tag(v_x_2946_) == 1)
{
lean_object* v_fvarId_2947_; lean_object* v___x_2948_; 
v_fvarId_2947_ = lean_ctor_get(v_x_2946_, 0);
lean_inc(v_fvarId_2947_);
lean_dec_ref_known(v_x_2946_, 1);
v___x_2948_ = lean_local_ctx_find(v_lctx_2944_, v_fvarId_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
uint8_t v___x_2949_; 
v___x_2949_ = 0;
return v___x_2949_;
}
else
{
lean_object* v_val_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v_val_2950_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_val_2950_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2951_ = l_Lean_LocalDecl_userName(v_val_2950_);
lean_dec(v_val_2950_);
v___x_2952_ = lean_name_eq(v___x_2951_, v_suggestion_x27_2945_);
lean_dec(v___x_2951_);
return v___x_2952_;
}
}
else
{
uint8_t v___x_2953_; 
lean_dec_ref(v_x_2946_);
lean_dec_ref(v_lctx_2944_);
v___x_2953_ = 0;
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed(lean_object* v_lctx_2954_, lean_object* v_suggestion_x27_2955_, lean_object* v_x_2956_){
_start:
{
uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_res_2957_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0(v_lctx_2954_, v_suggestion_x27_2955_, v_x_2956_);
lean_dec(v_suggestion_x27_2955_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* v_body_2959_, lean_object* v_lctx_2960_, lean_object* v_suggestion_x27_2961_){
_start:
{
lean_object* v___f_2962_; lean_object* v___x_2963_; 
v___f_2962_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2962_, 0, v_lctx_2960_);
lean_closure_set(v___f_2962_, 1, v_suggestion_x27_2961_);
v___x_2963_ = lean_find_expr(v___f_2962_, v_body_2959_);
lean_dec_ref(v___f_2962_);
if (lean_obj_tag(v___x_2963_) == 0)
{
uint8_t v___x_2964_; 
v___x_2964_ = 0;
return v___x_2964_;
}
else
{
uint8_t v___x_2965_; 
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = 1;
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* v_body_2966_, lean_object* v_lctx_2967_, lean_object* v_suggestion_x27_2968_){
_start:
{
uint8_t v_res_2969_; lean_object* v_r_2970_; 
v_res_2969_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2966_, v_lctx_2967_, v_suggestion_x27_2968_);
lean_dec_ref(v_body_2966_);
v_r_2970_ = lean_box(v_res_2969_);
return v_r_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(lean_object* v_snd_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_toCold_2975_; lean_object* v_quotContext_2976_; lean_object* v_currMacroScope_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_toCold_2975_ = lean_ctor_get(v___y_2972_, 0);
lean_inc_ref(v_toCold_2975_);
lean_dec_ref(v___y_2972_);
v_quotContext_2976_ = lean_ctor_get(v_toCold_2975_, 8);
lean_inc(v_quotContext_2976_);
v_currMacroScope_2977_ = lean_ctor_get(v_toCold_2975_, 9);
lean_inc(v_currMacroScope_2977_);
lean_dec_ref(v_toCold_2975_);
v___x_2978_ = l_Lean_addMacroScope(v_quotContext_2976_, v_snd_2971_, v_currMacroScope_2977_);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed(lean_object* v_snd_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0(v_snd_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* v_suggestion_2989_, lean_object* v_body_2990_, uint8_t v_preserveName_2991_, lean_object* v_avoid_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; uint8_t v_fst_3032_; lean_object* v_snd_3033_; uint8_t v___x_3039_; 
v___x_3039_ = l_Lean_Name_isAnonymous(v_suggestion_2989_);
if (v___x_3039_ == 0)
{
uint8_t v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = l_Lean_Name_hasMacroScopes(v_suggestion_2989_);
v___x_3041_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2989_);
v_fst_3032_ = v___x_3040_;
v_snd_3033_ = v___x_3041_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2));
v_fst_3032_ = v___x_3039_;
v_snd_3033_ = v___x_3042_;
goto v___jp_3031_;
}
v___jp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = l_Lean_LocalContext_getUnusedName(v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
v___jp_3005_:
{
if (v_preserveName_2991_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec_ref(v___y_3008_);
v___x_3009_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__0));
v___x_3010_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3009_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3021_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3021_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3021_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
uint8_t v___x_3015_; 
v___x_3015_ = lean_unbox(v_a_3011_);
lean_dec(v_a_3011_);
if (v___x_3015_ == 0)
{
lean_del_object(v___x_3013_);
v___y_3001_ = v___y_3006_;
v___y_3002_ = v___y_3007_;
goto v___jp_3000_;
}
else
{
uint8_t v___x_3016_; 
v___x_3016_ = l_Lean_NameSet_contains(v_avoid_2992_, v___y_3007_);
if (v___x_3016_ == 0)
{
uint8_t v___x_3017_; 
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
v___x_3017_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(v_body_2990_, v___y_3006_, v___y_3007_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3019_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___y_3007_);
v___x_3019_ = v___x_3013_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___y_3007_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
else
{
lean_del_object(v___x_3013_);
v___y_3001_ = v___y_3006_;
v___y_3002_ = v___y_3007_;
goto v___jp_3000_;
}
}
else
{
lean_del_object(v___x_3013_);
v___y_3001_ = v___y_3006_;
v___y_3002_ = v___y_3007_;
goto v___jp_3000_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v___y_3007_);
v_a_3022_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3010_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3010_);
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
lean_object* v___x_3030_; 
lean_dec(v___y_3007_);
v___x_3030_ = l_Lean_Core_withFreshMacroScope___redArg(v___y_3008_, v_a_2997_, v_a_2998_);
return v___x_3030_;
}
}
v___jp_3031_:
{
lean_object* v_lctx_3034_; uint8_t v___x_3035_; 
v_lctx_3034_ = lean_ctor_get(v_a_2995_, 2);
v___x_3035_ = l_Lean_LocalContext_usesUserName(v_lctx_3034_, v_snd_3033_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3036_, 0, v_snd_3033_);
return v___x_3036_;
}
else
{
lean_object* v___f_3037_; 
lean_inc(v_snd_3033_);
v___f_3037_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3037_, 0, v_snd_3033_);
if (v_preserveName_2991_ == 0)
{
v___y_3006_ = v_lctx_3034_;
v___y_3007_ = v_snd_3033_;
v___y_3008_ = v___f_3037_;
goto v___jp_3005_;
}
else
{
if (v_fst_3032_ == 0)
{
lean_object* v___x_3038_; 
lean_dec_ref(v___f_3037_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_snd_3033_);
return v___x_3038_;
}
else
{
v___y_3006_ = v_lctx_3034_;
v___y_3007_ = v_snd_3033_;
v___y_3008_ = v___f_3037_;
goto v___jp_3005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* v_suggestion_3043_, lean_object* v_body_3044_, lean_object* v_preserveName_3045_, lean_object* v_avoid_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
uint8_t v_preserveName_boxed_3054_; lean_object* v_res_3055_; 
v_preserveName_boxed_3054_ = lean_unbox(v_preserveName_3045_);
v_res_3055_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v_suggestion_3043_, v_body_3044_, v_preserveName_boxed_3054_, v_avoid_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_avoid_3046_);
lean_dec_ref(v_body_3044_);
lean_dec(v_suggestion_3043_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; lean_object* v_holeIter_3059_; lean_object* v_curr_3060_; lean_object* v___x_3061_; lean_object* v_steps_3062_; lean_object* v_infos_3063_; lean_object* v_holeIter_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3074_; 
v___x_3058_ = lean_st_ref_get(v___y_3056_);
v_holeIter_3059_ = lean_ctor_get(v___x_3058_, 2);
lean_inc_ref(v_holeIter_3059_);
lean_dec(v___x_3058_);
v_curr_3060_ = lean_ctor_get(v_holeIter_3059_, 0);
lean_inc(v_curr_3060_);
lean_dec_ref(v_holeIter_3059_);
v___x_3061_ = lean_st_ref_take(v___y_3056_);
v_steps_3062_ = lean_ctor_get(v___x_3061_, 0);
v_infos_3063_ = lean_ctor_get(v___x_3061_, 1);
v_holeIter_3064_ = lean_ctor_get(v___x_3061_, 2);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3066_ = v___x_3061_;
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_holeIter_3064_);
lean_inc(v_infos_3063_);
lean_inc(v_steps_3062_);
lean_dec(v___x_3061_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3068_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_holeIter_3064_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 2, v___x_3068_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_steps_3062_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_infos_3063_);
lean_ctor_set(v_reuseFailAlloc_3073_, 2, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_st_ref_put(v___y_3056_, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_curr_3060_);
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg___boxed(lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3075_);
lean_dec(v___y_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v___y_3079_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___boxed(lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0(v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(lean_object* v_n_3094_, lean_object* v_e_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3103_; lean_object* v_a_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; 
v___x_3103_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___at___00Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent_spec__0___redArg(v_a_3097_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_n(v_a_3104_, 2);
lean_dec_ref(v___x_3103_);
v___x_3105_ = l_Lean_mkIdent(v_n_3094_);
v___x_3106_ = l_Lean_PrettyPrinter_Delaborator_annotatePos(v_a_3104_, v___x_3105_);
v___x_3107_ = 0;
lean_inc(v___x_3106_);
v___x_3108_ = l_Lean_PrettyPrinter_Delaborator_addTermInfo___redArg(v_a_3104_, v___x_3106_, v_e_3095_, v___x_3107_, v_a_3097_, v_a_3098_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3108_, 0);
lean_dec(v_unused_3116_);
v___x_3110_ = v___x_3108_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_dec(v___x_3108_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3106_);
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3106_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec(v___x_3106_);
v_a_3117_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3108_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3108_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed(lean_object* v_n_3125_, lean_object* v_e_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent(v_n_3125_, v_e_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(lean_object* v_d_3135_, lean_object* v_x_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v___x_3144_; 
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
lean_inc(v___y_3140_);
lean_inc_ref(v___y_3139_);
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
v___x_3144_ = lean_apply_8(v_d_3135_, v_x_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, lean_box(0));
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed(lean_object* v_d_3145_, lean_object* v_x_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0(v_d_3145_, v_x_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(lean_object* v_k_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; 
lean_inc(v___y_3162_);
lean_inc_ref(v___y_3161_);
lean_inc(v___y_3160_);
lean_inc_ref(v___y_3159_);
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
v___x_3164_ = lean_apply_8(v_k_3155_, v_b_3158_, v___y_3156_, v___y_3157_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, lean_box(0));
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_k_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v_b_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0(v_k_3165_, v___y_3166_, v___y_3167_, v_b_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(lean_object* v_name_3175_, uint8_t v_bi_3176_, lean_object* v_type_3177_, lean_object* v_k_3178_, uint8_t v_kind_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___f_3187_; lean_object* v___x_3188_; 
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
v___f_3187_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3187_, 0, v_k_3178_);
lean_closure_set(v___f_3187_, 1, v___y_3180_);
lean_closure_set(v___f_3187_, 2, v___y_3181_);
v___x_3188_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3175_, v_bi_3176_, v_type_3177_, v___f_3187_, v_kind_3179_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3188_) == 0)
{
return v___x_3188_;
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg___boxed(lean_object* v_name_3197_, lean_object* v_bi_3198_, lean_object* v_type_3199_, lean_object* v_k_3200_, lean_object* v_kind_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v_bi_boxed_3209_; uint8_t v_kind_boxed_3210_; lean_object* v_res_3211_; 
v_bi_boxed_3209_ = lean_unbox(v_bi_3198_);
v_kind_boxed_3210_ = lean_unbox(v_kind_3201_);
v_res_3211_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3197_, v_bi_boxed_3209_, v_type_3199_, v_k_3200_, v_kind_boxed_3210_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(lean_object* v_child_3212_, lean_object* v_childIdx_3213_, lean_object* v_x_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_subExpr_3222_; lean_object* v_optionsPerPos_3223_; lean_object* v_currNamespace_3224_; lean_object* v_openDecls_3225_; uint8_t v_inPattern_3226_; lean_object* v_depth_3227_; lean_object* v_lctxInitIndices_3228_; lean_object* v_pos_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_subExpr_3222_ = lean_ctor_get(v___y_3215_, 3);
v_optionsPerPos_3223_ = lean_ctor_get(v___y_3215_, 0);
v_currNamespace_3224_ = lean_ctor_get(v___y_3215_, 1);
v_openDecls_3225_ = lean_ctor_get(v___y_3215_, 2);
v_inPattern_3226_ = lean_ctor_get_uint8(v___y_3215_, sizeof(void*)*6);
v_depth_3227_ = lean_ctor_get(v___y_3215_, 4);
v_lctxInitIndices_3228_ = lean_ctor_get(v___y_3215_, 5);
v_pos_3229_ = lean_ctor_get(v_subExpr_3222_, 1);
v___x_3230_ = l_Lean_SubExpr_Pos_push(v_pos_3229_, v_childIdx_3213_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_child_3212_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
lean_inc(v_lctxInitIndices_3228_);
lean_inc(v_depth_3227_);
lean_inc(v_openDecls_3225_);
lean_inc(v_currNamespace_3224_);
lean_inc(v_optionsPerPos_3223_);
v___x_3232_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3232_, 0, v_optionsPerPos_3223_);
lean_ctor_set(v___x_3232_, 1, v_currNamespace_3224_);
lean_ctor_set(v___x_3232_, 2, v_openDecls_3225_);
lean_ctor_set(v___x_3232_, 3, v___x_3231_);
lean_ctor_set(v___x_3232_, 4, v_depth_3227_);
lean_ctor_set(v___x_3232_, 5, v_lctxInitIndices_3228_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*6, v_inPattern_3226_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
v___x_3233_ = lean_apply_7(v_x_3214_, v___x_3232_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, lean_box(0));
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg___boxed(lean_object* v_child_3234_, lean_object* v_childIdx_3235_, lean_object* v_x_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3234_, v_childIdx_3235_, v_x_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(lean_object* v_v_3245_, lean_object* v_a_3246_, lean_object* v_x_3247_, lean_object* v_fvar_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v___x_3256_; 
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3253_);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3251_);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
lean_inc_ref(v_fvar_3248_);
v___x_3256_ = lean_apply_8(v_v_3245_, v_fvar_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, lean_box(0));
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = l_Lean_Expr_bindingBody_x21(v_a_3246_);
v___x_3259_ = lean_expr_instantiate1(v___x_3258_, v_fvar_3248_);
lean_dec_ref(v_fvar_3248_);
lean_dec_ref(v___x_3258_);
v___x_3260_ = lean_unsigned_to_nat(1u);
v___x_3261_ = lean_apply_1(v_x_3247_, v_a_3257_);
v___x_3262_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v___x_3259_, v___x_3260_, v___x_3261_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
return v___x_3262_;
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v_fvar_3248_);
lean_dec_ref(v_x_3247_);
v_a_3263_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3256_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3256_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed(lean_object* v_v_3271_, lean_object* v_a_3272_, lean_object* v_x_3273_, lean_object* v_fvar_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0(v_v_3271_, v_a_3272_, v_x_3273_, v_fvar_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v_a_3272_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(lean_object* v_n_3283_, lean_object* v_v_3284_, lean_object* v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; lean_object* v_a_3294_; lean_object* v___f_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3293_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_3286_);
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc_n(v_a_3294_, 2);
lean_dec_ref(v___x_3293_);
v___f_3295_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3295_, 0, v_v_3284_);
lean_closure_set(v___f_3295_, 1, v_a_3294_);
lean_closure_set(v___f_3295_, 2, v_x_3285_);
v___x_3296_ = l_Lean_Expr_binderInfo(v_a_3294_);
v___x_3297_ = l_Lean_Expr_bindingDomain_x21(v_a_3294_);
lean_dec(v_a_3294_);
v___x_3298_ = 0;
v___x_3299_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_n_3283_, v___x_3296_, v___x_3297_, v___f_3295_, v___x_3298_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg___boxed(lean_object* v_n_3300_, lean_object* v_v_3301_, lean_object* v_x_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3300_, v_v_3301_, v_x_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(lean_object* v_d_3311_, uint8_t v_preserveName_3312_, lean_object* v_avoid_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3321_; lean_object* v_a_3322_; lean_object* v___x_3323_; lean_object* v_a_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3321_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3314_);
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref(v___x_3321_);
v___x_3323_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3314_);
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = l_Lean_Expr_bindingName_x21(v_a_3322_);
lean_dec(v_a_3322_);
v___x_3326_ = l_Lean_Expr_bindingBody_x21(v_a_3324_);
lean_dec(v_a_3324_);
v___x_3327_ = l_Lean_PrettyPrinter_Delaborator_getUnusedName(v___x_3325_, v___x_3326_, v_preserveName_3312_, v_avoid_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
lean_dec_ref(v___x_3326_);
lean_dec(v___x_3325_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___f_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc_n(v_a_3328_, 2);
lean_dec_ref_known(v___x_3327_, 1);
v___f_3329_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3329_, 0, v_d_3311_);
v___x_3330_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAnnotatedIdent___boxed), 9, 1);
lean_closure_set(v___x_3330_, 0, v_a_3328_);
v___x_3331_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_a_3328_, v___x_3330_, v___f_3329_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
return v___x_3331_;
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref(v_d_3311_);
v_a_3332_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3327_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3327_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg___boxed(lean_object* v_d_3340_, lean_object* v_preserveName_3341_, lean_object* v_avoid_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
uint8_t v_preserveName_boxed_3350_; lean_object* v_res_3351_; 
v_preserveName_boxed_3350_ = lean_unbox(v_preserveName_3341_);
v_res_3351_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3340_, v_preserveName_boxed_3350_, v_avoid_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_avoid_3342_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* v_00_u03b1_3352_, lean_object* v_d_3353_, uint8_t v_preserveName_3354_, lean_object* v_avoid_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___redArg(v_d_3353_, v_preserveName_3354_, v_avoid_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___boxed(lean_object* v_00_u03b1_3364_, lean_object* v_d_3365_, lean_object* v_preserveName_3366_, lean_object* v_avoid_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
uint8_t v_preserveName_boxed_3375_; lean_object* v_res_3376_; 
v_preserveName_boxed_3375_ = lean_unbox(v_preserveName_3366_);
v_res_3376_ = l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(v_00_u03b1_3364_, v_d_3365_, v_preserveName_boxed_3375_, v_avoid_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_avoid_3367_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(lean_object* v_00_u03b1_3377_, lean_object* v_child_3378_, lean_object* v_childIdx_3379_, lean_object* v_x_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_child_3378_, v_childIdx_3379_, v_x_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3389_, lean_object* v_child_3390_, lean_object* v_childIdx_3391_, lean_object* v_x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0(v_00_u03b1_3389_, v_child_3390_, v_childIdx_3391_, v_x_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(lean_object* v_00_u03b1_3401_, lean_object* v_name_3402_, uint8_t v_bi_3403_, lean_object* v_type_3404_, lean_object* v_k_3405_, uint8_t v_kind_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___redArg(v_name_3402_, v_bi_3403_, v_type_3404_, v_k_3405_, v_kind_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3415_, lean_object* v_name_3416_, lean_object* v_bi_3417_, lean_object* v_type_3418_, lean_object* v_k_3419_, lean_object* v_kind_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v_bi_boxed_3428_; uint8_t v_kind_boxed_3429_; lean_object* v_res_3430_; 
v_bi_boxed_3428_ = lean_unbox(v_bi_3417_);
v_kind_boxed_3429_ = lean_unbox(v_kind_3420_);
v_res_3430_ = l_Lean_Meta_withLocalDecl___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__1(v_00_u03b1_3415_, v_name_3416_, v_bi_boxed_3428_, v_type_3418_, v_k_3419_, v_kind_boxed_3429_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(lean_object* v_00_u03b1_3431_, lean_object* v_00_u03b2_3432_, lean_object* v_n_3433_, lean_object* v_v_3434_, lean_object* v_x_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___redArg(v_n_3433_, v_v_3434_, v_x_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0___boxed(lean_object* v_00_u03b1_3444_, lean_object* v_00_u03b2_3445_, lean_object* v_n_3446_, lean_object* v_v_3447_, lean_object* v_x_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0(v_00_u03b1_3444_, v_00_u03b2_3445_, v_n_3446_, v_v_3447_, v_x_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(lean_object* v_x_3457_){
_start:
{
switch(lean_obj_tag(v_x_3457_))
{
case 0:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_unsigned_to_nat(0u);
return v___x_3458_;
}
case 1:
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_unsigned_to_nat(1u);
return v___x_3459_;
}
case 2:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_unsigned_to_nat(2u);
return v___x_3460_;
}
default: 
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_unsigned_to_nat(3u);
return v___x_3461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx___boxed(lean_object* v_x_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorIdx(v_x_3462_);
lean_dec(v_x_3462_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(lean_object* v_t_3464_, lean_object* v_k_3465_){
_start:
{
if (lean_obj_tag(v_t_3464_) == 3)
{
lean_object* v_s_3466_; lean_object* v___x_3467_; 
v_s_3466_ = lean_ctor_get(v_t_3464_, 0);
lean_inc_ref(v_s_3466_);
lean_dec_ref_known(v_t_3464_, 1);
v___x_3467_ = lean_apply_1(v_k_3465_, v_s_3466_);
return v___x_3467_;
}
else
{
lean_dec(v_t_3464_);
return v_k_3465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(lean_object* v_motive_3468_, lean_object* v_ctorIdx_3469_, lean_object* v_t_3470_, lean_object* v_h_3471_, lean_object* v_k_3472_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3470_, v_k_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___boxed(lean_object* v_motive_3474_, lean_object* v_ctorIdx_3475_, lean_object* v_t_3476_, lean_object* v_h_3477_, lean_object* v_k_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim(v_motive_3474_, v_ctorIdx_3475_, v_t_3476_, v_h_3477_, v_k_3478_);
lean_dec(v_ctorIdx_3475_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim___redArg(lean_object* v_t_3480_, lean_object* v_deep_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3480_, v_deep_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_deep_elim(lean_object* v_motive_3483_, lean_object* v_t_3484_, lean_object* v_h_3485_, lean_object* v_deep_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3484_, v_deep_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim___redArg(lean_object* v_t_3488_, lean_object* v_proof_3489_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3488_, v_proof_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_proof_elim(lean_object* v_motive_3491_, lean_object* v_t_3492_, lean_object* v_h_3493_, lean_object* v_proof_3494_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3492_, v_proof_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim___redArg(lean_object* v_t_3496_, lean_object* v_maxSteps_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3496_, v_maxSteps_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_maxSteps_elim(lean_object* v_motive_3499_, lean_object* v_t_3500_, lean_object* v_h_3501_, lean_object* v_maxSteps_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3500_, v_maxSteps_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim___redArg(lean_object* v_t_3504_, lean_object* v_string_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3504_, v_string_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_string_elim(lean_object* v_motive_3507_, lean_object* v_t_3508_, lean_object* v_h_3509_, lean_object* v_string_3510_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_ctorElim___redArg(v_t_3508_, v_string_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(lean_object* v_x_3515_){
_start:
{
switch(lean_obj_tag(v_x_3515_))
{
case 0:
{
lean_object* v___x_3516_; 
v___x_3516_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__0));
return v___x_3516_;
}
case 1:
{
lean_object* v___x_3517_; 
v___x_3517_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__1));
return v___x_3517_;
}
case 2:
{
lean_object* v___x_3518_; 
v___x_3518_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___closed__2));
return v___x_3518_;
}
default: 
{
lean_object* v_s_3519_; 
v_s_3519_ = lean_ctor_get(v_x_3515_, 0);
lean_inc_ref(v_s_3519_);
return v_s_3519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString___boxed(lean_object* v_x_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_x_3520_);
lean_dec(v_x_3520_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(lean_object* v_pos_3522_, lean_object* v_stx_3523_, lean_object* v_e_3524_, lean_object* v_reason_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3529_ = 0;
v___x_3530_ = lean_box(0);
v___x_3531_ = l_Lean_PrettyPrinter_Delaborator_OmissionReason_toString(v_reason_3525_);
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
v___x_3533_ = l_Lean_PrettyPrinter_Delaborator_addDelabTermInfo___redArg(v_pos_3522_, v_stx_3523_, v_e_3524_, v___x_3529_, v___x_3530_, v___x_3532_, v___x_3530_, v___x_3529_, v_a_3526_, v_a_3527_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg___boxed(lean_object* v_pos_3534_, lean_object* v_stx_3535_, lean_object* v_e_3536_, lean_object* v_reason_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3534_, v_stx_3535_, v_e_3536_, v_reason_3537_, v_a_3538_, v_a_3539_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec(v_reason_3537_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(lean_object* v_pos_3542_, lean_object* v_stx_3543_, lean_object* v_e_3544_, lean_object* v_reason_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_pos_3542_, v_stx_3543_, v_e_3544_, v_reason_3545_, v_a_3547_, v_a_3548_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___boxed(lean_object* v_pos_3554_, lean_object* v_stx_3555_, lean_object* v_e_3556_, lean_object* v_reason_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo(v_pos_3554_, v_stx_3555_, v_e_3556_, v_reason_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_reason_3557_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(lean_object* v_act_3566_, lean_object* v_ctx_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v_optionsPerPos_3574_; lean_object* v_currNamespace_3575_; lean_object* v_openDecls_3576_; uint8_t v_inPattern_3577_; lean_object* v_subExpr_3578_; lean_object* v_depth_3579_; lean_object* v_lctxInitIndices_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_optionsPerPos_3574_ = lean_ctor_get(v_ctx_3567_, 0);
v_currNamespace_3575_ = lean_ctor_get(v_ctx_3567_, 1);
v_openDecls_3576_ = lean_ctor_get(v_ctx_3567_, 2);
v_inPattern_3577_ = lean_ctor_get_uint8(v_ctx_3567_, sizeof(void*)*6);
v_subExpr_3578_ = lean_ctor_get(v_ctx_3567_, 3);
v_depth_3579_ = lean_ctor_get(v_ctx_3567_, 4);
v_lctxInitIndices_3580_ = lean_ctor_get(v_ctx_3567_, 5);
v___x_3581_ = lean_unsigned_to_nat(1u);
v___x_3582_ = lean_nat_add(v_depth_3579_, v___x_3581_);
lean_inc(v_lctxInitIndices_3580_);
lean_inc_ref(v_subExpr_3578_);
lean_inc(v_openDecls_3576_);
lean_inc(v_currNamespace_3575_);
lean_inc(v_optionsPerPos_3574_);
v___x_3583_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_3583_, 0, v_optionsPerPos_3574_);
lean_ctor_set(v___x_3583_, 1, v_currNamespace_3575_);
lean_ctor_set(v___x_3583_, 2, v_openDecls_3576_);
lean_ctor_set(v___x_3583_, 3, v_subExpr_3578_);
lean_ctor_set(v___x_3583_, 4, v___x_3582_);
lean_ctor_set(v___x_3583_, 5, v_lctxInitIndices_3580_);
lean_ctor_set_uint8(v___x_3583_, sizeof(void*)*6, v_inPattern_3577_);
lean_inc(v_a_3572_);
lean_inc_ref(v_a_3571_);
lean_inc(v_a_3570_);
lean_inc_ref(v_a_3569_);
lean_inc(v_a_3568_);
v___x_3584_ = lean_apply_7(v_act_3566_, v___x_3583_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, lean_box(0));
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg___boxed(lean_object* v_act_3585_, lean_object* v_ctx_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3585_, v_ctx_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_ctx_3586_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth(lean_object* v_00_u03b1_3594_, lean_object* v_act_3595_, lean_object* v_ctx_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v_act_3595_, v_ctx_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withIncDepth___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_act_3605_, lean_object* v_ctx_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth(v_00_u03b1_3604_, v_act_3605_, v_ctx_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_ctx_3606_);
return v_res_3613_;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isShallowExpression(lean_object* v_threshold_3614_, lean_object* v_e_3615_){
_start:
{
lean_object* v___y_3617_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3621_ = lean_unsigned_to_nat(254u);
v___x_3622_ = lean_nat_dec_le(v___x_3621_, v_threshold_3614_);
if (v___x_3622_ == 0)
{
v___y_3617_ = v_threshold_3614_;
goto v___jp_3616_;
}
else
{
v___y_3617_ = v___x_3621_;
goto v___jp_3616_;
}
v___jp_3616_:
{
uint32_t v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3618_ = l_Lean_Expr_approxDepth(v_e_3615_);
v___x_3619_ = lean_uint32_to_nat(v___x_3618_);
v___x_3620_ = lean_nat_dec_le(v___x_3619_, v___y_3617_);
lean_dec(v___x_3619_);
return v___x_3620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isShallowExpression___boxed(lean_object* v_threshold_3623_, lean_object* v_e_3624_){
_start:
{
uint8_t v_res_3625_; lean_object* v_r_3626_; 
v_res_3625_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_threshold_3623_, v_e_3624_);
lean_dec_ref(v_e_3624_);
lean_dec(v_threshold_3623_);
v_r_3626_ = lean_box(v_res_3625_);
return v_r_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(lean_object* v_e_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
uint8_t v___x_3637_; 
v___x_3637_ = l_Lean_Expr_isAtomic(v_e_3629_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__0));
v___x_3639_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3638_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3682_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3682_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3682_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
uint8_t v___x_3644_; 
v___x_3644_ = lean_unbox(v_a_3640_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_del_object(v___x_3642_);
v___x_3645_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___closed__1));
v___x_3646_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3645_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3669_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3669_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3669_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_depth_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v_depth_3651_ = lean_ctor_get(v_a_3630_, 4);
v___x_3652_ = lean_nat_sub(v_depth_3651_, v_a_3647_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = lean_nat_dec_lt(v___x_3653_, v___x_3652_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3656_; 
lean_dec(v___x_3652_);
lean_dec(v_a_3647_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v_a_3640_);
v___x_3656_ = v___x_3649_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3640_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3658_ = lean_unsigned_to_nat(2u);
v___x_3659_ = lean_nat_shiftr(v_a_3647_, v___x_3658_);
lean_dec(v_a_3647_);
v___x_3660_ = lean_nat_sub(v___x_3659_, v___x_3652_);
lean_dec(v___x_3652_);
lean_dec(v___x_3659_);
v___x_3661_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v___x_3660_, v_e_3629_);
lean_dec(v___x_3660_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_dec(v_a_3640_);
v___x_3662_ = lean_box(v___x_3654_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v___x_3662_);
v___x_3664_ = v___x_3649_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
else
{
lean_object* v___x_3667_; 
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v_a_3640_);
v___x_3667_ = v___x_3649_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3640_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v_a_3640_);
v_a_3670_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3646_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3646_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
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
else
{
lean_object* v___x_3678_; lean_object* v___x_3680_; 
lean_dec(v_a_3640_);
v___x_3678_ = lean_box(v___x_3637_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3678_);
v___x_3680_ = v___x_3642_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
return v___x_3639_;
}
}
else
{
uint8_t v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = 0;
v___x_3684_ = lean_box(v___x_3683_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr___boxed(lean_object* v_e_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_e_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec_ref(v_e_3686_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(lean_object* v_e_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
uint8_t v___x_3705_; 
v___x_3705_ = l_Lean_Expr_isAtomic(v_e_3697_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__0));
v___x_3707_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3706_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3757_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3757_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3757_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___y_3713_; uint8_t v___x_3738_; 
v___x_3738_ = lean_unbox(v_a_3708_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; 
lean_del_object(v___x_3710_);
lean_inc_ref(v_e_3697_);
v___x_3739_ = l_Lean_Meta_isProof(v_e_3697_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3739_) == 0)
{
v___y_3713_ = v___x_3739_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3740_; uint8_t v___y_3742_; uint8_t v___x_3751_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
v___x_3751_ = l_Lean_Exception_isInterrupt(v_a_3740_);
if (v___x_3751_ == 0)
{
uint8_t v___x_3752_; 
v___x_3752_ = l_Lean_Exception_isRuntime(v_a_3740_);
v___y_3742_ = v___x_3752_;
goto v___jp_3741_;
}
else
{
lean_dec(v_a_3740_);
v___y_3742_ = v___x_3751_;
goto v___jp_3741_;
}
v___jp_3741_:
{
if (v___y_3742_ == 0)
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v_e_3697_);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v___x_3739_, 0);
lean_dec(v_unused_3750_);
v___x_3744_ = v___x_3739_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v___x_3739_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set_tag(v___x_3744_, 0);
lean_ctor_set(v___x_3744_, 0, v_a_3708_);
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3708_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
else
{
v___y_3713_ = v___x_3739_;
goto v___jp_3712_;
}
}
}
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3755_; 
lean_dec(v_a_3708_);
lean_dec_ref(v_e_3697_);
v___x_3753_ = lean_box(v___x_3705_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3753_);
v___x_3755_ = v___x_3710_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
v___jp_3712_:
{
if (lean_obj_tag(v___y_3713_) == 0)
{
lean_object* v_a_3714_; uint8_t v___x_3715_; 
v_a_3714_ = lean_ctor_get(v___y_3713_, 0);
v___x_3715_ = lean_unbox(v_a_3714_);
if (v___x_3715_ == 0)
{
lean_dec(v_a_3708_);
lean_dec_ref(v_e_3697_);
return v___y_3713_;
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_inc(v_a_3714_);
lean_dec_ref_known(v___y_3713_, 1);
v___x_3716_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___closed__1));
v___x_3717_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_3716_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3729_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3729_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3729_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
uint8_t v___x_3722_; 
v___x_3722_ = l_Lean_PrettyPrinter_Delaborator_isShallowExpression(v_a_3718_, v_e_3697_);
lean_dec_ref(v_e_3697_);
lean_dec(v_a_3718_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3724_; 
lean_dec(v_a_3708_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_a_3714_);
v___x_3724_ = v___x_3720_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3714_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
else
{
lean_object* v___x_3727_; 
lean_dec(v_a_3714_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_a_3708_);
v___x_3727_ = v___x_3720_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3708_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_a_3714_);
lean_dec(v_a_3708_);
lean_dec_ref(v_e_3697_);
v_a_3730_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3717_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3717_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
else
{
lean_dec(v_a_3708_);
lean_dec_ref(v_e_3697_);
return v___y_3713_;
}
}
}
}
else
{
lean_dec_ref(v_e_3697_);
return v___x_3707_;
}
}
else
{
uint8_t v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_dec_ref(v_e_3697_);
v___x_3758_ = 0;
v___x_3759_ = lean_box(v___x_3758_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_shouldOmitProof___boxed(lean_object* v_e_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_e_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg(lean_object* v_reason_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_ref_3784_; uint8_t v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_ref_3784_ = lean_ctor_get(v_a_3782_, 2);
v___x_3785_ = 0;
v___x_3786_ = l_Lean_SourceInfo_fromRef(v_ref_3784_, v___x_3785_);
v___x_3787_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__2));
v___x_3788_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_omission___redArg___closed__3));
lean_inc(v___x_3786_);
v___x_3789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3786_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = l_Lean_Syntax_node1(v___x_3786_, v___x_3787_, v___x_3789_);
v___x_3791_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_3790_, v_a_3779_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; lean_object* v_a_3794_; lean_object* v___x_3795_; lean_object* v_a_3796_; lean_object* v___x_3797_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc_n(v_a_3792_, 2);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at___00Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos_spec__1___redArg(v_a_3779_);
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_3779_);
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3795_);
v___x_3797_ = l_Lean_PrettyPrinter_Delaborator_addOmissionInfo___redArg(v_a_3794_, v_a_3792_, v_a_3796_, v_reason_3778_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; 
v_unused_3805_ = lean_ctor_get(v___x_3797_, 0);
lean_dec(v_unused_3805_);
v___x_3799_ = v___x_3797_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_dec(v___x_3797_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_a_3792_);
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3792_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_a_3792_);
v_a_3806_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3797_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3797_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
return v___x_3791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___redArg___boxed(lean_object* v_reason_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
lean_dec_ref(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec(v_reason_3814_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission(lean_object* v_reason_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v_reason_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3826_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_omission___boxed(lean_object* v_reason_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_PrettyPrinter_Delaborator_omission(v_reason_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_reason_3830_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(lean_object* v_x_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
if (lean_obj_tag(v_x_3839_) == 0)
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3847_;
}
else
{
lean_object* v_head_3848_; lean_object* v_tail_3849_; lean_object* v___x_3850_; 
v_head_3848_ = lean_ctor_get(v_x_3839_, 0);
lean_inc(v_head_3848_);
v_tail_3849_ = lean_ctor_get(v_x_3839_, 1);
lean_inc(v_tail_3849_);
lean_dec_ref_known(v_x_3839_, 2);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
v___x_3850_ = lean_apply_7(v_head_3848_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, lean_box(0));
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_dec(v_tail_3849_);
return v___x_3850_;
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3852_; uint8_t v___y_3854_; uint8_t v___x_3858_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
v___x_3852_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3858_ = l_Lean_Exception_isInterrupt(v_a_3851_);
if (v___x_3858_ == 0)
{
uint8_t v___x_3859_; 
lean_inc(v_a_3851_);
v___x_3859_ = l_Lean_Exception_isRuntime(v_a_3851_);
v___y_3854_ = v___x_3859_;
goto v___jp_3853_;
}
else
{
v___y_3854_ = v___x_3858_;
goto v___jp_3853_;
}
v___jp_3853_:
{
if (v___y_3854_ == 0)
{
if (lean_obj_tag(v_a_3851_) == 0)
{
lean_dec_ref_known(v_a_3851_, 2);
lean_dec(v_tail_3849_);
return v___x_3850_;
}
else
{
lean_object* v_id_3855_; uint8_t v___x_3856_; 
v_id_3855_ = lean_ctor_get(v_a_3851_, 0);
lean_inc(v_id_3855_);
lean_dec_ref_known(v_a_3851_, 2);
v___x_3856_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3852_, v_id_3855_);
lean_dec(v_id_3855_);
if (v___x_3856_ == 0)
{
lean_dec(v_tail_3849_);
return v___x_3850_;
}
else
{
lean_dec_ref_known(v___x_3850_, 1);
v_x_3839_ = v_tail_3849_;
goto _start;
}
}
}
else
{
lean_dec(v_a_3851_);
lean_dec(v_tail_3849_);
return v___x_3850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0___boxed(lean_object* v_x_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v_x_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* v_x_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; uint8_t v___y_3881_; lean_object* v___y_3889_; 
if (lean_obj_tag(v_x_3869_) == 0)
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3894_;
}
else
{
lean_object* v___x_3895_; lean_object* v_env_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3895_ = lean_st_ref_get(v_a_3875_);
v_env_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc_ref(v_env_3896_);
lean_dec(v___x_3895_);
v___x_3897_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_3898_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_3897_, v_env_3896_, v_x_3869_);
v___x_3899_ = l_List_firstM___at___00Lean_PrettyPrinter_Delaborator_delabFor_spec__0(v___x_3898_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = l_Lean_PrettyPrinter_Delaborator_annotateTermInfoUnlessAnnotated___redArg(v_a_3900_, v_a_3870_, v_a_3871_, v_a_3872_);
v___y_3889_ = v___x_3901_;
goto v___jp_3888_;
}
else
{
v___y_3889_ = v___x_3899_;
goto v___jp_3888_;
}
}
v___jp_3877_:
{
if (v___y_3881_ == 0)
{
if (lean_obj_tag(v___y_3880_) == 0)
{
lean_dec_ref_known(v___y_3880_, 2);
lean_dec(v_x_3869_);
return v___y_3878_;
}
else
{
lean_object* v_id_3882_; uint8_t v___x_3883_; 
v_id_3882_ = lean_ctor_get(v___y_3880_, 0);
lean_inc(v_id_3882_);
lean_dec_ref_known(v___y_3880_, 2);
v___x_3883_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3879_, v_id_3882_);
lean_dec(v_id_3882_);
if (v___x_3883_ == 0)
{
lean_dec(v_x_3869_);
return v___y_3878_;
}
else
{
uint8_t v___x_3884_; 
lean_dec_ref(v___y_3878_);
v___x_3884_ = l_Lean_Name_isAtomic(v_x_3869_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Name_getRoot(v_x_3869_);
lean_dec(v_x_3869_);
v_x_3869_ = v___x_3885_;
goto _start;
}
else
{
lean_object* v___x_3887_; 
lean_dec(v_x_3869_);
v___x_3887_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_3887_;
}
}
}
}
else
{
lean_dec_ref(v___y_3880_);
lean_dec(v_x_3869_);
return v___y_3878_;
}
}
v___jp_3888_:
{
if (lean_obj_tag(v___y_3889_) == 0)
{
lean_dec(v_x_3869_);
return v___y_3889_;
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; 
v_a_3890_ = lean_ctor_get(v___y_3889_, 0);
lean_inc(v_a_3890_);
v___x_3891_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3892_ = l_Lean_Exception_isInterrupt(v_a_3890_);
if (v___x_3892_ == 0)
{
uint8_t v___x_3893_; 
lean_inc(v_a_3890_);
v___x_3893_ = l_Lean_Exception_isRuntime(v_a_3890_);
v___y_3878_ = v___y_3889_;
v___y_3879_ = v___x_3891_;
v___y_3880_ = v_a_3890_;
v___y_3881_ = v___x_3893_;
goto v___jp_3877_;
}
else
{
v___y_3878_ = v___y_3889_;
v___y_3879_ = v___x_3891_;
v___y_3880_ = v_a_3890_;
v___y_3881_ = v___x_3892_;
goto v___jp_3877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___boxed(lean_object* v_x_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_x_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(lean_object* v_msgData_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; lean_object* v_env_3918_; lean_object* v___x_3919_; lean_object* v_toCold_3920_; lean_object* v_mctx_3921_; lean_object* v_lctx_3922_; lean_object* v_options_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3917_ = lean_st_ref_get(v___y_3915_);
v_env_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc_ref(v_env_3918_);
lean_dec(v___x_3917_);
v___x_3919_ = lean_st_ref_get(v___y_3913_);
v_toCold_3920_ = lean_ctor_get(v___y_3914_, 0);
v_mctx_3921_ = lean_ctor_get(v___x_3919_, 0);
lean_inc_ref(v_mctx_3921_);
lean_dec(v___x_3919_);
v_lctx_3922_ = lean_ctor_get(v___y_3912_, 2);
v_options_3923_ = lean_ctor_get(v_toCold_3920_, 2);
lean_inc_ref(v_options_3923_);
lean_inc_ref(v_lctx_3922_);
v___x_3924_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3924_, 0, v_env_3918_);
lean_ctor_set(v___x_3924_, 1, v_mctx_3921_);
lean_ctor_set(v___x_3924_, 2, v_lctx_3922_);
lean_ctor_set(v___x_3924_, 3, v_options_3923_);
v___x_3925_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v_msgData_3911_);
v___x_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0___boxed(lean_object* v_msgData_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msgData_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(lean_object* v_msg_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_ref_3940_; lean_object* v___x_3941_; lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3950_; 
v_ref_3940_ = lean_ctor_get(v___y_3937_, 2);
v___x_3941_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
lean_inc(v_ref_3940_);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v_ref_3940_);
lean_ctor_set(v___x_3946_, 1, v_a_3942_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set_tag(v___x_3944_, 1);
lean_ctor_set(v___x_3944_, 0, v___x_3946_);
v___x_3948_ = v___x_3944_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg___boxed(lean_object* v_msg_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3957_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__0));
v___x_3960_ = l_Lean_stringToMessageData(v___x_3959_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0(lean_object* v_a_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; 
lean_inc(v_a_3961_);
v___x_3969_ = l_Lean_PrettyPrinter_Delaborator_delabFor(v_a_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_dec(v_a_3961_);
return v___x_3969_;
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3971_; uint8_t v___y_3973_; uint8_t v___x_3989_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
v___x_3971_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_3989_ = l_Lean_Exception_isInterrupt(v_a_3970_);
if (v___x_3989_ == 0)
{
uint8_t v___x_3990_; 
lean_inc(v_a_3970_);
v___x_3990_ = l_Lean_Exception_isRuntime(v_a_3970_);
v___y_3973_ = v___x_3990_;
goto v___jp_3972_;
}
else
{
v___y_3973_ = v___x_3989_;
goto v___jp_3972_;
}
v___jp_3972_:
{
if (v___y_3973_ == 0)
{
if (lean_obj_tag(v_a_3970_) == 0)
{
lean_dec_ref_known(v_a_3970_, 2);
lean_dec(v_a_3961_);
return v___x_3969_;
}
else
{
lean_object* v_id_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3987_; 
v_id_3974_ = lean_ctor_get(v_a_3970_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_a_3970_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v_a_3970_, 1);
lean_dec(v_unused_3988_);
v___x_3976_ = v_a_3970_;
v_isShared_3977_ = v_isSharedCheck_3987_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_id_3974_);
lean_dec(v_a_3970_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3987_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
uint8_t v___x_3978_; 
v___x_3978_ = l_Lean_instBEqInternalExceptionId_beq(v___x_3971_, v_id_3974_);
lean_dec(v_id_3974_);
if (v___x_3978_ == 0)
{
lean_del_object(v___x_3976_);
lean_dec(v_a_3961_);
return v___x_3969_;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3982_; 
lean_dec_ref_known(v___x_3969_, 1);
v___x_3979_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1, &l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___lam__0___closed__1);
v___x_3980_ = l_Lean_MessageData_ofName(v_a_3961_);
if (v_isShared_3977_ == 0)
{
lean_ctor_set_tag(v___x_3976_, 7);
lean_ctor_set(v___x_3976_, 1, v___x_3980_);
lean_ctor_set(v___x_3976_, 0, v___x_3979_);
v___x_3982_ = v___x_3976_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3979_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3983_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__2_spec__6_spec__11_spec__14_spec__16___redArg___closed__3);
v___x_3984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v___x_3984_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
return v___x_3985_;
}
}
}
}
}
else
{
lean_dec(v_a_3970_);
lean_dec(v_a_3961_);
return v___x_3969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed(lean_object* v_a_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_PrettyPrinter_Delaborator_delab___lam__0(v_a_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(lean_object* v_x_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; lean_object* v_a_4009_; lean_object* v___x_4010_; 
v___x_4008_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v___y_4001_);
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref(v___x_4008_);
lean_inc(v___y_4006_);
lean_inc_ref(v___y_4005_);
lean_inc(v___y_4004_);
lean_inc_ref(v___y_4003_);
v___x_4010_ = lean_infer_type(v_a_4009_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = l_Lean_SubExpr_Pos_typeCoord;
v___x_4013_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___at___00Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName_spec__0_spec__0___redArg(v_a_4011_, v___x_4012_, v_x_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
return v___x_4013_;
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec_ref(v_x_4000_);
v_a_4014_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_4010_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4010_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg___boxed(lean_object* v_x_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4030_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4049_ = l_String_toRawSubstring_x27(v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_PrettyPrinter_Delaborator_delab(v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__4_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4108_ = l_Lean_Core_checkSystem(v___x_4107_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec_ref_known(v___x_4108_, 1);
v___x_4109_ = lean_st_ref_get(v_a_4101_);
v___x_4110_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__0));
v___x_4111_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4110_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v_steps_4113_; uint8_t v___x_4114_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v_steps_4113_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_steps_4113_);
lean_dec(v___x_4109_);
v___x_4114_ = lean_nat_dec_le(v_a_4112_, v_steps_4113_);
lean_dec(v_steps_4113_);
lean_dec(v_a_4112_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; lean_object* v_steps_4116_; lean_object* v_infos_4117_; lean_object* v_holeIter_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4291_; 
v___x_4115_ = lean_st_ref_take(v_a_4101_);
v_steps_4116_ = lean_ctor_get(v___x_4115_, 0);
v_infos_4117_ = lean_ctor_get(v___x_4115_, 1);
v_holeIter_4118_ = lean_ctor_get(v___x_4115_, 2);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4120_ = v___x_4115_;
v_isShared_4121_ = v_isSharedCheck_4291_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_holeIter_4118_);
lean_inc(v_infos_4117_);
lean_inc(v_steps_4116_);
lean_dec(v___x_4115_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4291_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4122_ = lean_unsigned_to_nat(1u);
v___x_4123_ = lean_nat_add(v_steps_4116_, v___x_4122_);
lean_dec(v_steps_4116_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4123_);
v___x_4125_ = v___x_4120_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4290_, 1, v_infos_4117_);
lean_ctor_set(v_reuseFailAlloc_4290_, 2, v_holeIter_4118_);
v___x_4125_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_st_ref_put(v_a_4101_, v___x_4125_);
v___x_4127_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_getExprKind_spec__0___redArg(v_a_4100_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v___x_4129_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitExpr(v_a_4128_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; uint8_t v___x_4131_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v___x_4131_ = lean_unbox(v_a_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
lean_inc(v_a_4128_);
v___x_4132_ = l_Lean_PrettyPrinter_Delaborator_shouldOmitProof(v_a_4128_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; uint8_t v___x_4134_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v___x_4134_ = lean_unbox(v_a_4133_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; 
lean_dec(v_a_4130_);
v___x_4135_ = l_Lean_PrettyPrinter_Delaborator_getExprKind(v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___f_4137_; lean_object* v___x_4138_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___f_4137_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4137_, 0, v_a_4136_);
v___x_4138_ = l_Lean_PrettyPrinter_Delaborator_withIncDepth___redArg(v___f_4137_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___y_4141_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4188_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__25));
v___x_4189_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4188_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; uint8_t v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
v___x_4191_ = lean_unbox(v_a_4190_);
lean_dec(v_a_4190_);
if (v___x_4191_ == 0)
{
lean_dec(v_a_4128_);
v___y_4141_ = v___x_4189_;
goto v___jp_4140_;
}
else
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
lean_dec_ref_known(v___x_4189_, 1);
v___x_4192_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__26));
v___x_4193_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4192_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; uint8_t v___x_4195_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
v___x_4195_ = lean_unbox(v_a_4194_);
lean_dec(v_a_4194_);
if (v___x_4195_ == 0)
{
lean_dec(v_a_4128_);
v___y_4141_ = v___x_4193_;
goto v___jp_4140_;
}
else
{
uint8_t v___x_4196_; 
v___x_4196_ = l_Lean_Expr_isMData(v_a_4128_);
lean_dec(v_a_4128_);
if (v___x_4196_ == 0)
{
v___y_4141_ = v___x_4193_;
goto v___jp_4140_;
}
else
{
lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_dec(v_a_4133_);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4203_ == 0)
{
lean_object* v_unused_4204_; 
v_unused_4204_ = lean_ctor_get(v___x_4193_, 0);
lean_dec(v_unused_4204_);
v___x_4198_ = v___x_4193_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_dec(v___x_4193_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v_a_4139_);
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4139_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
}
else
{
lean_dec(v_a_4128_);
v___y_4141_ = v___x_4193_;
goto v___jp_4140_;
}
}
}
else
{
lean_dec(v_a_4128_);
v___y_4141_ = v___x_4189_;
goto v___jp_4140_;
}
v___jp_4140_:
{
if (lean_obj_tag(v___y_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4179_; 
v_a_4142_ = lean_ctor_get(v___y_4141_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___y_4141_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4144_ = v___y_4141_;
v_isShared_4145_ = v_isSharedCheck_4179_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___y_4141_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4179_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_unbox(v_a_4142_);
lean_dec(v_a_4142_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4148_; 
lean_dec(v_a_4133_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v_a_4139_);
v___x_4148_ = v___x_4144_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4139_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_del_object(v___x_4144_);
v___x_4150_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4151_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4150_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_toCold_4152_; lean_object* v_a_4153_; lean_object* v_ref_4154_; lean_object* v_quotContext_4155_; lean_object* v_currMacroScope_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_toCold_4152_ = lean_ctor_get(v_a_4104_, 0);
v_a_4153_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4151_, 1);
v_ref_4154_ = lean_ctor_get(v_a_4104_, 2);
v_quotContext_4155_ = lean_ctor_get(v_toCold_4152_, 8);
v_currMacroScope_4156_ = lean_ctor_get(v_toCold_4152_, 9);
v___x_4157_ = lean_unbox(v_a_4133_);
lean_dec(v_a_4133_);
v___x_4158_ = l_Lean_SourceInfo_fromRef(v_ref_4154_, v___x_4157_);
v___x_4159_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4160_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4161_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4158_, 7);
v___x_4162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4158_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v___x_4163_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4164_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4165_ = lean_box(0);
lean_inc(v_currMacroScope_4156_);
lean_inc(v_quotContext_4155_);
v___x_4166_ = l_Lean_addMacroScope(v_quotContext_4155_, v___x_4165_, v_currMacroScope_4156_);
v___x_4167_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4168_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4158_);
lean_ctor_set(v___x_4168_, 1, v___x_4164_);
lean_ctor_set(v___x_4168_, 2, v___x_4166_);
lean_ctor_set(v___x_4168_, 3, v___x_4167_);
v___x_4169_ = l_Lean_Syntax_node1(v___x_4158_, v___x_4163_, v___x_4168_);
v___x_4170_ = l_Lean_Syntax_node2(v___x_4158_, v___x_4160_, v___x_4162_, v___x_4169_);
v___x_4171_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4158_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4174_ = l_Lean_Syntax_node1(v___x_4158_, v___x_4173_, v_a_4153_);
v___x_4175_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4158_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = l_Lean_Syntax_node5(v___x_4158_, v___x_4159_, v___x_4170_, v_a_4139_, v___x_4172_, v___x_4174_, v___x_4176_);
v___x_4178_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4177_, v_a_4100_);
return v___x_4178_;
}
else
{
lean_dec(v_a_4139_);
lean_dec(v_a_4133_);
return v___x_4151_;
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec(v_a_4139_);
lean_dec(v_a_4133_);
v_a_4180_ = lean_ctor_get(v___y_4141_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___y_4141_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___y_4141_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___y_4141_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
}
else
{
lean_dec(v_a_4133_);
lean_dec(v_a_4128_);
return v___x_4138_;
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec(v_a_4133_);
lean_dec(v_a_4128_);
v_a_4205_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4135_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4135_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_dec(v_a_4133_);
lean_dec(v_a_4128_);
v___x_4213_ = lean_box(1);
v___x_4214_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4213_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4104_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v___x_4216_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__27));
v___x_4217_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4216_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4255_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4255_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4255_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
uint8_t v___x_4222_; 
v___x_4222_ = lean_unbox(v_a_4218_);
lean_dec(v_a_4218_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4224_; 
lean_dec(v_a_4130_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v_a_4215_);
v___x_4224_ = v___x_4220_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4215_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
else
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_del_object(v___x_4220_);
v___x_4226_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab___boxed), 7, 0);
v___x_4227_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v___x_4226_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_toCold_4228_; lean_object* v_a_4229_; lean_object* v_ref_4230_; lean_object* v_quotContext_4231_; lean_object* v_currMacroScope_4232_; uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v_toCold_4228_ = lean_ctor_get(v_a_4104_, 0);
v_a_4229_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4227_, 1);
v_ref_4230_ = lean_ctor_get(v_a_4104_, 2);
v_quotContext_4231_ = lean_ctor_get(v_toCold_4228_, 8);
v_currMacroScope_4232_ = lean_ctor_get(v_toCold_4228_, 9);
v___x_4233_ = lean_unbox(v_a_4130_);
lean_dec(v_a_4130_);
v___x_4234_ = l_Lean_SourceInfo_fromRef(v_ref_4230_, v___x_4233_);
v___x_4235_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__2));
v___x_4236_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__4));
v___x_4237_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__5));
lean_inc_n(v___x_4234_, 7);
v___x_4238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4234_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
v___x_4239_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__7));
v___x_4240_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_delab___closed__8, &l_Lean_PrettyPrinter_Delaborator_delab___closed__8_once, _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__8);
v___x_4241_ = lean_box(0);
lean_inc(v_currMacroScope_4232_);
lean_inc(v_quotContext_4231_);
v___x_4242_ = l_Lean_addMacroScope(v_quotContext_4231_, v___x_4241_, v_currMacroScope_4232_);
v___x_4243_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__22));
v___x_4244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4234_);
lean_ctor_set(v___x_4244_, 1, v___x_4240_);
lean_ctor_set(v___x_4244_, 2, v___x_4242_);
lean_ctor_set(v___x_4244_, 3, v___x_4243_);
v___x_4245_ = l_Lean_Syntax_node1(v___x_4234_, v___x_4239_, v___x_4244_);
v___x_4246_ = l_Lean_Syntax_node2(v___x_4234_, v___x_4236_, v___x_4238_, v___x_4245_);
v___x_4247_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__23));
v___x_4248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4234_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1___closed__3_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_));
v___x_4250_ = l_Lean_Syntax_node1(v___x_4234_, v___x_4249_, v_a_4229_);
v___x_4251_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delab___closed__24));
v___x_4252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4234_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = l_Lean_Syntax_node5(v___x_4234_, v___x_4235_, v___x_4246_, v_a_4215_, v___x_4248_, v___x_4250_, v___x_4252_);
v___x_4254_ = l_Lean_PrettyPrinter_Delaborator_annotateCurPos___redArg(v___x_4253_, v_a_4100_);
return v___x_4254_;
}
else
{
lean_dec(v_a_4215_);
lean_dec(v_a_4130_);
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v_a_4215_);
lean_dec(v_a_4130_);
v_a_4256_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4217_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4217_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_dec(v_a_4130_);
return v___x_4214_;
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_a_4130_);
lean_dec(v_a_4128_);
v_a_4264_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4132_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4132_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec(v_a_4130_);
lean_dec(v_a_4128_);
v___x_4272_ = lean_box(0);
v___x_4273_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4272_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4104_);
return v___x_4273_;
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec(v_a_4128_);
v_a_4274_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4129_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4129_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
v_a_4282_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4127_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4127_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
}
}
else
{
lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4292_ = lean_box(2);
v___x_4293_ = l_Lean_PrettyPrinter_Delaborator_omission___redArg(v___x_4292_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4104_);
return v___x_4293_;
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_dec(v___x_4109_);
v_a_4294_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4111_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4111_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_a_4302_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4108_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4108_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(lean_object* v_00_u03b1_4310_, lean_object* v_msg_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___redArg(v_msg_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0___boxed(lean_object* v_00_u03b1_4318_, lean_object* v_msg_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0(v_00_u03b1_4318_, v_msg_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(lean_object* v_00_u03b1_4326_, lean_object* v_x_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___redArg(v_x_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1___boxed(lean_object* v_00_u03b1_4336_, lean_object* v_x_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at___00Lean_PrettyPrinter_Delaborator_delab_spec__1(v_00_u03b1_4336_, v_x_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel(lean_object* v_l_4347_, lean_object* v_prec_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4356_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_delabLevel___closed__0));
v___x_4357_ = l_Lean_PrettyPrinter_Delaborator_getPPOption___redArg(v___x_4356_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4370_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4360_ = v___x_4357_;
v_isShared_4361_ = v_isSharedCheck_4370_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4357_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4370_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4362_; lean_object* v_mctx_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4368_; 
v___x_4362_ = lean_st_ref_get(v_a_4352_);
v_mctx_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc_ref(v_mctx_4363_);
lean_dec(v___x_4362_);
v___x_4364_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4364_, 0, v_mctx_4363_);
v___x_4365_ = lean_unbox(v_a_4358_);
lean_dec(v_a_4358_);
v___x_4366_ = l_Lean_Level_quote(v_l_4347_, v_prec_4348_, v___x_4365_, v___x_4364_);
if (v_isShared_4361_ == 0)
{
lean_ctor_set(v___x_4360_, 0, v___x_4366_);
v___x_4368_ = v___x_4360_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_l_4347_);
v_a_4371_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4357_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4357_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabLevel___boxed(lean_object* v_l_4379_, lean_object* v_prec_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_PrettyPrinter_Delaborator_delabLevel(v_l_4379_, v_prec_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec(v_a_4382_);
lean_dec_ref(v_a_4381_);
lean_dec(v_prec_4380_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(uint8_t v_x_4389_, lean_object* v_stx_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_Attribute_Builtin_getIdent(v_stx_4390_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v___x_4396_ = lean_box(0);
v___x_4397_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_4395_, v___x_4396_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; uint8_t v___x_4399_; lean_object* v___x_4400_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc_n(v_a_4398_, 2);
lean_dec_ref_known(v___x_4397_, 1);
v___x_4399_ = 0;
v___x_4400_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1(v_a_4398_, v___x_4399_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4407_ == 0)
{
lean_object* v_unused_4408_; 
v_unused_4408_ = lean_ctor_get(v___x_4400_, 0);
lean_dec(v_unused_4408_);
v___x_4402_ = v___x_4400_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_dec(v___x_4400_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v_a_4398_);
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4398_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_a_4398_);
v_a_4409_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4400_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4400_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
else
{
return v___x_4397_;
}
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
v_a_4417_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4394_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4394_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_x_4425_, lean_object* v_stx_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
uint8_t v_x_409__boxed_4430_; lean_object* v_res_4431_; 
v_x_409__boxed_4430_ = lean_unbox(v_x_4425_);
v_res_4431_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___lam__1_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(v_x_409__boxed_4430_, v_stx_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4456_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__6_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4457_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4458_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_4456_, v___x_4457_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2____boxed(lean_object* v_a_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1(){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4463_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4464_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___closed__0));
v___x_4465_ = l_Lean_addBuiltinDocString(v___x_4463_, v___x_4464_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1___boxed(lean_object* v_a_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3(){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn___closed__8_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_));
v___x_4495_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___closed__6));
v___x_4496_ = l_Lean_addBuiltinDeclarationRanges(v___x_4494_, v___x_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3___boxed(lean_object* v_a_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(lean_object* v_l_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; lean_object* v_mctx_4503_; lean_object* v___x_4504_; lean_object* v_fst_4505_; lean_object* v_snd_4506_; lean_object* v___x_4507_; lean_object* v_cache_4508_; lean_object* v_zetaDeltaFVarIds_4509_; lean_object* v_postponed_4510_; lean_object* v_diag_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4520_; 
v___x_4502_ = lean_st_ref_get(v___y_4500_);
v_mctx_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc_ref(v_mctx_4503_);
lean_dec(v___x_4502_);
v___x_4504_ = lean_instantiate_level_mvars(v_mctx_4503_, v_l_4499_);
v_fst_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_fst_4505_);
v_snd_4506_ = lean_ctor_get(v___x_4504_, 1);
lean_inc(v_snd_4506_);
lean_dec_ref(v___x_4504_);
v___x_4507_ = lean_st_ref_take(v___y_4500_);
v_cache_4508_ = lean_ctor_get(v___x_4507_, 1);
v_zetaDeltaFVarIds_4509_ = lean_ctor_get(v___x_4507_, 2);
v_postponed_4510_ = lean_ctor_get(v___x_4507_, 3);
v_diag_4511_ = lean_ctor_get(v___x_4507_, 4);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4520_ == 0)
{
lean_object* v_unused_4521_; 
v_unused_4521_ = lean_ctor_get(v___x_4507_, 0);
lean_dec(v_unused_4521_);
v___x_4513_ = v___x_4507_;
v_isShared_4514_ = v_isSharedCheck_4520_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_diag_4511_);
lean_inc(v_postponed_4510_);
lean_inc(v_zetaDeltaFVarIds_4509_);
lean_inc(v_cache_4508_);
lean_dec(v___x_4507_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4520_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v_fst_4505_);
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_fst_4505_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_cache_4508_);
lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_zetaDeltaFVarIds_4509_);
lean_ctor_set(v_reuseFailAlloc_4519_, 3, v_postponed_4510_);
lean_ctor_set(v_reuseFailAlloc_4519_, 4, v_diag_4511_);
v___x_4516_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_st_ref_put(v___y_4500_, v___x_4516_);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v_snd_4506_);
return v___x_4518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg___boxed(lean_object* v_l_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4522_, v___y_4523_);
lean_dec(v___y_4523_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(lean_object* v_l_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4526_, v___y_4528_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___boxed(lean_object* v_l_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0(v_l_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object* v_l_4540_, lean_object* v_prec_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_l_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v_toCold_4559_; lean_object* v_options_4560_; uint8_t v___x_4561_; 
v_toCold_4559_ = lean_ctor_get(v_a_4544_, 0);
v_options_4560_ = lean_ctor_get(v_toCold_4559_, 2);
v___x_4561_ = l_Lean_getPPInstantiateMVars(v_options_4560_);
if (v___x_4561_ == 0)
{
v_l_4548_ = v_l_4540_;
v___y_4549_ = v_a_4543_;
v___y_4550_ = v_a_4544_;
goto v___jp_4547_;
}
else
{
lean_object* v___x_4562_; lean_object* v_a_4563_; 
v___x_4562_ = l_Lean_instantiateLevelMVars___at___00Lean_PrettyPrinter_delabLevel_spec__0___redArg(v_l_4540_, v_a_4543_);
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref(v___x_4562_);
v_l_4548_ = v_a_4563_;
v___y_4549_ = v_a_4543_;
v___y_4550_ = v_a_4544_;
goto v___jp_4547_;
}
v___jp_4547_:
{
lean_object* v___x_4551_; lean_object* v_toCold_4552_; lean_object* v_options_4553_; lean_object* v_mctx_4554_; uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4551_ = lean_st_ref_get(v___y_4549_);
v_toCold_4552_ = lean_ctor_get(v___y_4550_, 0);
v_options_4553_ = lean_ctor_get(v_toCold_4552_, 2);
v_mctx_4554_ = lean_ctor_get(v___x_4551_, 0);
lean_inc_ref(v_mctx_4554_);
lean_dec(v___x_4551_);
v___x_4555_ = l_Lean_getPPMVarsLevels(v_options_4553_);
v___x_4556_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_4556_, 0, v_mctx_4554_);
v___x_4557_ = l_Lean_Level_quote(v_l_4548_, v_prec_4541_, v___x_4555_, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
return v___x_4558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabLevel___boxed(lean_object* v_l_4564_, lean_object* v_prec_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_PrettyPrinter_delabLevel(v_l_4564_, v_prec_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_prec_4565_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(lean_object* v_msg_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___f_4579_; lean_object* v___x_7827__overap_4580_; lean_object* v___x_4581_; 
v___f_4579_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___closed__0));
v___x_7827__overap_4580_ = lean_panic_fn_borrowed(v___f_4579_, v_msg_4573_);
lean_inc(v___y_4577_);
lean_inc_ref(v___y_4576_);
lean_inc(v___y_4575_);
lean_inc_ref(v___y_4574_);
v___x_4581_ = lean_apply_5(v___x_7827__overap_4580_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, lean_box(0));
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg___boxed(lean_object* v_msg_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(lean_object* v_00_u03b1_4589_, lean_object* v_msg_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v___x_4596_; 
v___x_4596_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v_msg_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___boxed(lean_object* v_00_u03b1_4597_, lean_object* v_msg_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0(v_00_u03b1_4597_, v_msg_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
return v_res_4604_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(lean_object* v_opts_4605_, lean_object* v_opt_4606_){
_start:
{
lean_object* v_name_4607_; lean_object* v_defValue_4608_; lean_object* v_map_4609_; lean_object* v___x_4610_; 
v_name_4607_ = lean_ctor_get(v_opt_4606_, 0);
v_defValue_4608_ = lean_ctor_get(v_opt_4606_, 1);
v_map_4609_ = lean_ctor_get(v_opts_4605_, 0);
v___x_4610_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4609_, v_name_4607_);
if (lean_obj_tag(v___x_4610_) == 0)
{
uint8_t v___x_4611_; 
v___x_4611_ = lean_unbox(v_defValue_4608_);
return v___x_4611_;
}
else
{
lean_object* v_val_4612_; 
v_val_4612_ = lean_ctor_get(v___x_4610_, 0);
lean_inc(v_val_4612_);
lean_dec_ref_known(v___x_4610_, 1);
if (lean_obj_tag(v_val_4612_) == 1)
{
uint8_t v_v_4613_; 
v_v_4613_ = lean_ctor_get_uint8(v_val_4612_, 0);
lean_dec_ref_known(v_val_4612_, 0);
return v_v_4613_;
}
else
{
uint8_t v___x_4614_; 
lean_dec(v_val_4612_);
v___x_4614_ = lean_unbox(v_defValue_4608_);
return v___x_4614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1___boxed(lean_object* v_opts_4615_, lean_object* v_opt_4616_){
_start:
{
uint8_t v_res_4617_; lean_object* v_r_4618_; 
v_res_4617_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_4615_, v_opt_4616_);
lean_dec_ref(v_opt_4616_);
lean_dec_ref(v_opts_4615_);
v_r_4618_ = lean_box(v_res_4617_);
return v_r_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(lean_object* v_opts_4619_, lean_object* v_opt_4620_){
_start:
{
lean_object* v_name_4621_; lean_object* v_defValue_4622_; lean_object* v_map_4623_; lean_object* v___x_4624_; 
v_name_4621_ = lean_ctor_get(v_opt_4620_, 0);
v_defValue_4622_ = lean_ctor_get(v_opt_4620_, 1);
v_map_4623_ = lean_ctor_get(v_opts_4619_, 0);
v___x_4624_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4623_, v_name_4621_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_inc(v_defValue_4622_);
return v_defValue_4622_;
}
else
{
lean_object* v_val_4625_; 
v_val_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_val_4625_);
lean_dec_ref_known(v___x_4624_, 1);
if (lean_obj_tag(v_val_4625_) == 3)
{
lean_object* v_v_4626_; 
v_v_4626_ = lean_ctor_get(v_val_4625_, 0);
lean_inc(v_v_4626_);
lean_dec_ref_known(v_val_4625_, 1);
return v_v_4626_;
}
else
{
lean_dec(v_val_4625_);
lean_inc(v_defValue_4622_);
return v_defValue_4622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2___boxed(lean_object* v_opts_4627_, lean_object* v_opt_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v_opts_4627_, v_opt_4628_);
lean_dec_ref(v_opt_4628_);
lean_dec_ref(v_opts_4627_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(lean_object* v_e_4630_, lean_object* v___y_4631_){
_start:
{
uint8_t v___x_4633_; 
v___x_4633_ = l_Lean_Expr_hasMVar(v_e_4630_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v_e_4630_);
return v___x_4634_;
}
else
{
lean_object* v___x_4635_; lean_object* v_mctx_4636_; lean_object* v___x_4637_; lean_object* v_fst_4638_; lean_object* v_snd_4639_; lean_object* v___x_4640_; lean_object* v_cache_4641_; lean_object* v_zetaDeltaFVarIds_4642_; lean_object* v_postponed_4643_; lean_object* v_diag_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4653_; 
v___x_4635_ = lean_st_ref_get(v___y_4631_);
v_mctx_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc_ref(v_mctx_4636_);
lean_dec(v___x_4635_);
v___x_4637_ = l_Lean_instantiateMVarsCore(v_mctx_4636_, v_e_4630_);
v_fst_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_fst_4638_);
v_snd_4639_ = lean_ctor_get(v___x_4637_, 1);
lean_inc(v_snd_4639_);
lean_dec_ref(v___x_4637_);
v___x_4640_ = lean_st_ref_take(v___y_4631_);
v_cache_4641_ = lean_ctor_get(v___x_4640_, 1);
v_zetaDeltaFVarIds_4642_ = lean_ctor_get(v___x_4640_, 2);
v_postponed_4643_ = lean_ctor_get(v___x_4640_, 3);
v_diag_4644_ = lean_ctor_get(v___x_4640_, 4);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4653_ == 0)
{
lean_object* v_unused_4654_; 
v_unused_4654_ = lean_ctor_get(v___x_4640_, 0);
lean_dec(v_unused_4654_);
v___x_4646_ = v___x_4640_;
v_isShared_4647_ = v_isSharedCheck_4653_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_diag_4644_);
lean_inc(v_postponed_4643_);
lean_inc(v_zetaDeltaFVarIds_4642_);
lean_inc(v_cache_4641_);
lean_dec(v___x_4640_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4653_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 0, v_snd_4639_);
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_snd_4639_);
lean_ctor_set(v_reuseFailAlloc_4652_, 1, v_cache_4641_);
lean_ctor_set(v_reuseFailAlloc_4652_, 2, v_zetaDeltaFVarIds_4642_);
lean_ctor_set(v_reuseFailAlloc_4652_, 3, v_postponed_4643_);
lean_ctor_set(v_reuseFailAlloc_4652_, 4, v_diag_4644_);
v___x_4649_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = lean_st_ref_put(v___y_4631_, v___x_4649_);
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v_fst_4638_);
return v___x_4651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg___boxed(lean_object* v_e_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4655_, v___y_4656_);
lean_dec(v___y_4656_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(lean_object* v_e_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_e_4659_, v___y_4661_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___boxed(lean_object* v_e_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3(v_e_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(lean_object* v_opts_4673_, lean_object* v_opt_4674_){
_start:
{
lean_object* v_name_4675_; lean_object* v_map_4676_; lean_object* v___x_4677_; 
v_name_4675_ = lean_ctor_get(v_opt_4674_, 0);
v_map_4676_ = lean_ctor_get(v_opts_4673_, 0);
v___x_4677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4676_, v_name_4675_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_box(0);
return v___x_4678_;
}
else
{
lean_object* v_val_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4689_; 
v_val_4679_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4681_ = v___x_4677_;
v_isShared_4682_ = v_isSharedCheck_4689_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_val_4679_);
lean_dec(v___x_4677_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4689_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
if (lean_obj_tag(v_val_4679_) == 1)
{
uint8_t v_v_4683_; lean_object* v___x_4684_; lean_object* v___x_4686_; 
v_v_4683_ = lean_ctor_get_uint8(v_val_4679_, 0);
lean_dec_ref_known(v_val_4679_, 0);
v___x_4684_ = lean_box(v_v_4683_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v___x_4684_);
v___x_4686_ = v___x_4681_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
else
{
lean_object* v___x_4688_; 
lean_del_object(v___x_4681_);
lean_dec(v_val_4679_);
v___x_4688_ = lean_box(0);
return v___x_4688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5___boxed(lean_object* v_opts_4690_, lean_object* v_opt_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_opts_4690_, v_opt_4691_);
lean_dec_ref(v_opt_4691_);
lean_dec_ref(v_opts_4690_);
return v_res_4692_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(lean_object* v_x_4693_, lean_object* v_x_4694_){
_start:
{
if (lean_obj_tag(v_x_4693_) == 0)
{
if (lean_obj_tag(v_x_4694_) == 0)
{
uint8_t v___x_4695_; 
v___x_4695_ = 1;
return v___x_4695_;
}
else
{
uint8_t v___x_4696_; 
v___x_4696_ = 0;
return v___x_4696_;
}
}
else
{
if (lean_obj_tag(v_x_4694_) == 0)
{
uint8_t v___x_4697_; 
v___x_4697_ = 0;
return v___x_4697_;
}
else
{
lean_object* v_val_4698_; uint8_t v___x_4699_; 
v_val_4698_ = lean_ctor_get(v_x_4694_, 0);
v___x_4699_ = lean_unbox(v_val_4698_);
if (v___x_4699_ == 0)
{
lean_object* v_val_4700_; uint8_t v___x_4701_; 
v_val_4700_ = lean_ctor_get(v_x_4693_, 0);
v___x_4701_ = lean_unbox(v_val_4700_);
if (v___x_4701_ == 0)
{
uint8_t v___x_4702_; 
v___x_4702_ = 1;
return v___x_4702_;
}
else
{
uint8_t v___x_4703_; 
v___x_4703_ = lean_unbox(v_val_4698_);
return v___x_4703_;
}
}
else
{
lean_object* v_val_4704_; uint8_t v___x_4705_; 
v_val_4704_ = lean_ctor_get(v_x_4693_, 0);
v___x_4705_ = lean_unbox(v_val_4704_);
return v___x_4705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6___boxed(lean_object* v_x_4706_, lean_object* v_x_4707_){
_start:
{
uint8_t v_res_4708_; lean_object* v_r_4709_; 
v_res_4708_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v_x_4706_, v_x_4707_);
lean_dec(v_x_4707_);
lean_dec(v_x_4706_);
v_r_4709_ = lean_box(v_res_4708_);
return v_r_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(lean_object* v_o_4710_, lean_object* v_k_4711_, uint8_t v_v_4712_){
_start:
{
lean_object* v_map_4713_; uint8_t v_hasTrace_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4728_; 
v_map_4713_ = lean_ctor_get(v_o_4710_, 0);
v_hasTrace_4714_ = lean_ctor_get_uint8(v_o_4710_, sizeof(void*)*1);
v_isSharedCheck_4728_ = !lean_is_exclusive(v_o_4710_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4716_ = v_o_4710_;
v_isShared_4717_ = v_isSharedCheck_4728_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_map_4713_);
lean_dec(v_o_4710_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4728_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4718_, 0, v_v_4712_);
lean_inc(v_k_4711_);
v___x_4719_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4711_, v___x_4718_, v_map_4713_);
if (v_hasTrace_4714_ == 0)
{
lean_object* v___x_4720_; uint8_t v___x_4721_; lean_object* v___x_4723_; 
v___x_4720_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14));
v___x_4721_ = l_Lean_Name_isPrefixOf(v___x_4720_, v_k_4711_);
lean_dec(v_k_4711_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4719_);
v___x_4723_ = v___x_4716_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4719_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*1, v___x_4721_);
return v___x_4723_;
}
}
else
{
lean_object* v___x_4726_; 
lean_dec(v_k_4711_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4719_);
v___x_4726_ = v___x_4716_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v___x_4719_);
lean_ctor_set_uint8(v_reuseFailAlloc_4727_, sizeof(void*)*1, v_hasTrace_4714_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4___boxed(lean_object* v_o_4729_, lean_object* v_k_4730_, lean_object* v_v_4731_){
_start:
{
uint8_t v_v_boxed_4732_; lean_object* v_res_4733_; 
v_v_boxed_4732_ = lean_unbox(v_v_4731_);
v_res_4733_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_o_4729_, v_k_4730_, v_v_boxed_4732_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(lean_object* v_opts_4734_, lean_object* v_opt_4735_, uint8_t v_val_4736_){
_start:
{
lean_object* v_name_4737_; lean_object* v___x_4738_; 
v_name_4737_ = lean_ctor_get(v_opt_4735_, 0);
lean_inc(v_name_4737_);
lean_dec_ref(v_opt_4735_);
v___x_4738_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4_spec__4(v_opts_4734_, v_name_4737_, v_val_4736_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4___boxed(lean_object* v_opts_4739_, lean_object* v_opt_4740_, lean_object* v_val_4741_){
_start:
{
uint8_t v_val_boxed_4742_; lean_object* v_res_4743_; 
v_val_boxed_4742_ = lean_unbox(v_val_4741_);
v_res_4743_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v_opts_4739_, v_opt_4740_, v_val_boxed_4742_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(lean_object* v_cls_4744_, lean_object* v_msg_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
lean_object* v_ref_4751_; lean_object* v___x_4752_; lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4797_; 
v_ref_4751_ = lean_ctor_get(v___y_4748_, 2);
v___x_4752_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_PrettyPrinter_Delaborator_delab_spec__0_spec__0(v_msg_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4755_ = v___x_4752_;
v_isShared_4756_ = v_isSharedCheck_4797_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4752_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4797_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4757_; lean_object* v_traceState_4758_; lean_object* v_env_4759_; lean_object* v_nextMacroScope_4760_; lean_object* v_ngen_4761_; lean_object* v_auxDeclNGen_4762_; lean_object* v_cache_4763_; lean_object* v_messages_4764_; lean_object* v_infoState_4765_; lean_object* v_snapshotTasks_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4796_; 
v___x_4757_ = lean_st_ref_take(v___y_4749_);
v_traceState_4758_ = lean_ctor_get(v___x_4757_, 4);
v_env_4759_ = lean_ctor_get(v___x_4757_, 0);
v_nextMacroScope_4760_ = lean_ctor_get(v___x_4757_, 1);
v_ngen_4761_ = lean_ctor_get(v___x_4757_, 2);
v_auxDeclNGen_4762_ = lean_ctor_get(v___x_4757_, 3);
v_cache_4763_ = lean_ctor_get(v___x_4757_, 5);
v_messages_4764_ = lean_ctor_get(v___x_4757_, 6);
v_infoState_4765_ = lean_ctor_get(v___x_4757_, 7);
v_snapshotTasks_4766_ = lean_ctor_get(v___x_4757_, 8);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4768_ = v___x_4757_;
v_isShared_4769_ = v_isSharedCheck_4796_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_snapshotTasks_4766_);
lean_inc(v_infoState_4765_);
lean_inc(v_messages_4764_);
lean_inc(v_cache_4763_);
lean_inc(v_traceState_4758_);
lean_inc(v_auxDeclNGen_4762_);
lean_inc(v_ngen_4761_);
lean_inc(v_nextMacroScope_4760_);
lean_inc(v_env_4759_);
lean_dec(v___x_4757_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4796_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
uint64_t v_tid_4770_; lean_object* v_traces_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4795_; 
v_tid_4770_ = lean_ctor_get_uint64(v_traceState_4758_, sizeof(void*)*1);
v_traces_4771_ = lean_ctor_get(v_traceState_4758_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v_traceState_4758_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4773_ = v_traceState_4758_;
v_isShared_4774_ = v_isSharedCheck_4795_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_traces_4771_);
lean_dec(v_traceState_4758_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4795_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4775_; double v___x_4776_; uint8_t v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4775_ = lean_box(0);
v___x_4776_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__0);
v___x_4777_ = 0;
v___x_4778_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__1));
v___x_4779_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4779_, 0, v_cls_4744_);
lean_ctor_set(v___x_4779_, 1, v___x_4775_);
lean_ctor_set(v___x_4779_, 2, v___x_4778_);
lean_ctor_set_float(v___x_4779_, sizeof(void*)*3, v___x_4776_);
lean_ctor_set_float(v___x_4779_, sizeof(void*)*3 + 8, v___x_4776_);
lean_ctor_set_uint8(v___x_4779_, sizeof(void*)*3 + 16, v___x_4777_);
v___x_4780_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2_spec__5___closed__2));
v___x_4781_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4779_);
lean_ctor_set(v___x_4781_, 1, v_a_4753_);
lean_ctor_set(v___x_4781_, 2, v___x_4780_);
lean_inc(v_ref_4751_);
v___x_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4782_, 0, v_ref_4751_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
v___x_4783_ = l_Lean_PersistentArray_push___redArg(v_traces_4771_, v___x_4782_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v___x_4783_);
v___x_4785_ = v___x_4773_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4783_);
lean_ctor_set_uint64(v_reuseFailAlloc_4794_, sizeof(void*)*1, v_tid_4770_);
v___x_4785_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4787_; 
if (v_isShared_4769_ == 0)
{
lean_ctor_set(v___x_4768_, 4, v___x_4785_);
v___x_4787_ = v___x_4768_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_env_4759_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v_nextMacroScope_4760_);
lean_ctor_set(v_reuseFailAlloc_4793_, 2, v_ngen_4761_);
lean_ctor_set(v_reuseFailAlloc_4793_, 3, v_auxDeclNGen_4762_);
lean_ctor_set(v_reuseFailAlloc_4793_, 4, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4793_, 5, v_cache_4763_);
lean_ctor_set(v_reuseFailAlloc_4793_, 6, v_messages_4764_);
lean_ctor_set(v_reuseFailAlloc_4793_, 7, v_infoState_4765_);
lean_ctor_set(v_reuseFailAlloc_4793_, 8, v_snapshotTasks_4766_);
v___x_4787_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4791_; 
v___x_4788_ = lean_st_ref_put(v___y_4749_, v___x_4787_);
v___x_4789_ = lean_box(0);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 0, v___x_4789_);
v___x_4791_ = v___x_4755_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7___boxed(lean_object* v_cls_4798_, lean_object* v_msg_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(v_cls_4798_, v_msg_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
return v_res_4805_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4809_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__2));
v___x_4810_ = lean_unsigned_to_nat(18u);
v___x_4811_ = lean_unsigned_to_nat(536u);
v___x_4812_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__1));
v___x_4813_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__0));
v___x_4814_ = l_mkPanicMessageWithDecl(v___x_4813_, v___x_4812_, v___x_4811_, v___x_4810_, v___x_4809_);
return v___x_4814_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4(void){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4815_ = l_Lean_SubExpr_Pos_maxChildren;
v___x_4816_ = lean_unsigned_to_nat(2u);
v___x_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
lean_ctor_set(v___x_4817_, 1, v___x_4815_);
return v___x_4817_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4818_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__4, &l_Lean_PrettyPrinter_delabCore___redArg___closed__4_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__4);
v___x_4819_ = lean_box(1);
v___x_4820_ = lean_unsigned_to_nat(0u);
v___x_4821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
lean_ctor_set(v___x_4821_, 1, v___x_4819_);
lean_ctor_set(v___x_4821_, 2, v___x_4818_);
return v___x_4821_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4827_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_4828_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__14));
v___x_4829_ = l_Lean_Name_append(v___x_4828_, v___x_4827_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object* v_e_4830_, lean_object* v_optionsPerPos_4831_, lean_object* v_delab_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_fst_4839_; lean_object* v_snd_4840_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4850_; uint8_t v___y_4851_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v_optionsPerPos_4873_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v___y_4876_; lean_object* v___y_4877_; lean_object* v___y_4902_; lean_object* v_e_4903_; lean_object* v___y_4904_; lean_object* v___y_4905_; lean_object* v___y_4906_; lean_object* v___y_4907_; lean_object* v___y_4921_; lean_object* v_e_4922_; lean_object* v___y_4923_; lean_object* v___y_4924_; lean_object* v___y_4925_; lean_object* v___y_4926_; lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_Meta_erasePatternRefAnnotations(v_e_4830_, v_a_4835_, v_a_4836_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_5069_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_4941_ = v___x_4938_;
v_isShared_4942_ = v_isSharedCheck_5069_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4938_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_5069_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
uint8_t v___y_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v___y_4947_; uint8_t v___y_4948_; lean_object* v___y_4949_; lean_object* v___y_4950_; uint8_t v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v___y_4976_; lean_object* v___y_4977_; uint8_t v___y_4978_; uint8_t v___y_4979_; lean_object* v_opts_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v___y_5015_; lean_object* v___y_5016_; lean_object* v___y_5017_; lean_object* v___y_5018_; uint8_t v___y_5019_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v___y_5026_; lean_object* v___y_5027_; lean_object* v___y_5028_; lean_object* v___y_5029_; uint8_t v___y_5030_; lean_object* v___y_5040_; lean_object* v___y_5041_; lean_object* v___y_5042_; lean_object* v_options_5043_; lean_object* v___y_5044_; lean_object* v_toCold_5050_; lean_object* v_options_5051_; uint8_t v_hasTrace_5052_; 
v_toCold_5050_ = lean_ctor_get(v_a_4835_, 0);
v_options_5051_ = lean_ctor_get(v_toCold_5050_, 2);
v_hasTrace_5052_ = lean_ctor_get_uint8(v_options_5051_, sizeof(void*)*1);
if (v_hasTrace_5052_ == 0)
{
v___y_5040_ = v_a_4833_;
v___y_5041_ = v_a_4834_;
v___y_5042_ = v_a_4835_;
v_options_5043_ = v_options_5051_;
v___y_5044_ = v_a_4836_;
goto v___jp_5039_;
}
else
{
lean_object* v_inheritedTraceOptions_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; uint8_t v___x_5056_; 
v_inheritedTraceOptions_5053_ = lean_ctor_get(v_toCold_5050_, 11);
v___x_5054_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5055_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__8, &l_Lean_PrettyPrinter_delabCore___redArg___closed__8_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__8);
v___x_5056_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5053_, v_options_5051_, v___x_5055_);
if (v___x_5056_ == 0)
{
v___y_5040_ = v_a_4833_;
v___y_5041_ = v_a_4834_;
v___y_5042_ = v_a_4835_;
v_options_5043_ = v_options_5051_;
v___y_5044_ = v_a_4836_;
goto v___jp_5039_;
}
else
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5057_ = lean_expr_dbg_to_string(v_a_4939_);
v___x_5058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
v___x_5059_ = l_Lean_MessageData_ofFormat(v___x_5058_);
v___x_5060_ = l_Lean_addTrace___at___00Lean_PrettyPrinter_delabCore_spec__7(v___x_5054_, v___x_5059_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_dec_ref_known(v___x_5060_, 1);
v___y_5040_ = v_a_4833_;
v___y_5041_ = v_a_4834_;
v___y_5042_ = v_a_4835_;
v_options_5043_ = v_options_5051_;
v___y_5044_ = v_a_4836_;
goto v___jp_5039_;
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
lean_del_object(v___x_4941_);
lean_dec(v_a_4939_);
lean_dec_ref(v_delab_4832_);
lean_dec(v_optionsPerPos_4831_);
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5060_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5060_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
}
v___jp_4943_:
{
lean_object* v_toCold_4951_; lean_object* v_currRecDepth_4952_; lean_object* v_ref_4953_; uint8_t v_suppressElabErrors_4954_; lean_object* v_fileName_4955_; lean_object* v_fileMap_4956_; lean_object* v_currNamespace_4957_; lean_object* v_openDecls_4958_; lean_object* v_initHeartbeats_4959_; lean_object* v_maxHeartbeats_4960_; lean_object* v_quotContext_4961_; lean_object* v_currMacroScope_4962_; lean_object* v_cancelTk_x3f_4963_; lean_object* v_inheritedTraceOptions_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_toCold_4951_ = lean_ctor_get(v___y_4949_, 0);
v_currRecDepth_4952_ = lean_ctor_get(v___y_4949_, 1);
v_ref_4953_ = lean_ctor_get(v___y_4949_, 2);
v_suppressElabErrors_4954_ = lean_ctor_get_uint8(v___y_4949_, sizeof(void*)*3 + 1);
v_fileName_4955_ = lean_ctor_get(v_toCold_4951_, 0);
v_fileMap_4956_ = lean_ctor_get(v_toCold_4951_, 1);
v_currNamespace_4957_ = lean_ctor_get(v_toCold_4951_, 4);
v_openDecls_4958_ = lean_ctor_get(v_toCold_4951_, 5);
v_initHeartbeats_4959_ = lean_ctor_get(v_toCold_4951_, 6);
v_maxHeartbeats_4960_ = lean_ctor_get(v_toCold_4951_, 7);
v_quotContext_4961_ = lean_ctor_get(v_toCold_4951_, 8);
v_currMacroScope_4962_ = lean_ctor_get(v_toCold_4951_, 9);
v_cancelTk_x3f_4963_ = lean_ctor_get(v_toCold_4951_, 10);
v_inheritedTraceOptions_4964_ = lean_ctor_get(v_toCold_4951_, 11);
v___x_4965_ = l_Lean_maxRecDepth;
v___x_4966_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__2(v___y_4947_, v___x_4965_);
lean_inc_ref(v_inheritedTraceOptions_4964_);
lean_inc(v_cancelTk_x3f_4963_);
lean_inc(v_currMacroScope_4962_);
lean_inc(v_quotContext_4961_);
lean_inc(v_maxHeartbeats_4960_);
lean_inc(v_initHeartbeats_4959_);
lean_inc(v_openDecls_4958_);
lean_inc(v_currNamespace_4957_);
lean_inc_ref(v___y_4947_);
lean_inc_ref(v_fileMap_4956_);
lean_inc_ref(v_fileName_4955_);
v___x_4967_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4967_, 0, v_fileName_4955_);
lean_ctor_set(v___x_4967_, 1, v_fileMap_4956_);
lean_ctor_set(v___x_4967_, 2, v___y_4947_);
lean_ctor_set(v___x_4967_, 3, v___x_4966_);
lean_ctor_set(v___x_4967_, 4, v_currNamespace_4957_);
lean_ctor_set(v___x_4967_, 5, v_openDecls_4958_);
lean_ctor_set(v___x_4967_, 6, v_initHeartbeats_4959_);
lean_ctor_set(v___x_4967_, 7, v_maxHeartbeats_4960_);
lean_ctor_set(v___x_4967_, 8, v_quotContext_4961_);
lean_ctor_set(v___x_4967_, 9, v_currMacroScope_4962_);
lean_ctor_set(v___x_4967_, 10, v_cancelTk_x3f_4963_);
lean_ctor_set(v___x_4967_, 11, v_inheritedTraceOptions_4964_);
lean_inc(v_ref_4953_);
lean_inc(v_currRecDepth_4952_);
v___x_4968_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
lean_ctor_set(v___x_4968_, 1, v_currRecDepth_4952_);
lean_ctor_set(v___x_4968_, 2, v_ref_4953_);
lean_ctor_set_uint8(v___x_4968_, sizeof(void*)*3, v___y_4948_);
lean_ctor_set_uint8(v___x_4968_, sizeof(void*)*3 + 1, v_suppressElabErrors_4954_);
if (v___y_4944_ == 0)
{
v___y_4921_ = v___y_4947_;
v_e_4922_ = v_a_4939_;
v___y_4923_ = v___y_4946_;
v___y_4924_ = v___y_4945_;
v___y_4925_ = v___x_4968_;
v___y_4926_ = v___y_4950_;
goto v___jp_4920_;
}
else
{
lean_object* v___x_4969_; lean_object* v_a_4970_; 
v___x_4969_ = l_Lean_instantiateMVars___at___00Lean_PrettyPrinter_delabCore_spec__3___redArg(v_a_4939_, v___y_4945_);
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref(v___x_4969_);
v___y_4921_ = v___y_4947_;
v_e_4922_ = v_a_4970_;
v___y_4923_ = v___y_4946_;
v___y_4924_ = v___y_4945_;
v___y_4925_ = v___x_4968_;
v___y_4926_ = v___y_4950_;
goto v___jp_4920_;
}
}
v___jp_4971_:
{
if (v___y_4979_ == 0)
{
lean_object* v___x_4980_; lean_object* v_env_4981_; lean_object* v_nextMacroScope_4982_; lean_object* v_ngen_4983_; lean_object* v_auxDeclNGen_4984_; lean_object* v_traceState_4985_; lean_object* v_messages_4986_; lean_object* v_infoState_4987_; lean_object* v_snapshotTasks_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4998_; 
v___x_4980_ = lean_st_ref_take(v___y_4975_);
v_env_4981_ = lean_ctor_get(v___x_4980_, 0);
v_nextMacroScope_4982_ = lean_ctor_get(v___x_4980_, 1);
v_ngen_4983_ = lean_ctor_get(v___x_4980_, 2);
v_auxDeclNGen_4984_ = lean_ctor_get(v___x_4980_, 3);
v_traceState_4985_ = lean_ctor_get(v___x_4980_, 4);
v_messages_4986_ = lean_ctor_get(v___x_4980_, 6);
v_infoState_4987_ = lean_ctor_get(v___x_4980_, 7);
v_snapshotTasks_4988_ = lean_ctor_get(v___x_4980_, 8);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_4998_ == 0)
{
lean_object* v_unused_4999_; 
v_unused_4999_ = lean_ctor_get(v___x_4980_, 5);
lean_dec(v_unused_4999_);
v___x_4990_ = v___x_4980_;
v_isShared_4991_ = v_isSharedCheck_4998_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_snapshotTasks_4988_);
lean_inc(v_infoState_4987_);
lean_inc(v_messages_4986_);
lean_inc(v_traceState_4985_);
lean_inc(v_auxDeclNGen_4984_);
lean_inc(v_ngen_4983_);
lean_inc(v_nextMacroScope_4982_);
lean_inc(v_env_4981_);
lean_dec(v___x_4980_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4998_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4995_; 
v___x_4992_ = l_Lean_Kernel_enableDiag(v_env_4981_, v___y_4978_);
v___x_4993_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2__spec__1_spec__2___closed__5);
if (v_isShared_4991_ == 0)
{
lean_ctor_set(v___x_4990_, 5, v___x_4993_);
lean_ctor_set(v___x_4990_, 0, v___x_4992_);
v___x_4995_ = v___x_4990_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4992_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v_nextMacroScope_4982_);
lean_ctor_set(v_reuseFailAlloc_4997_, 2, v_ngen_4983_);
lean_ctor_set(v_reuseFailAlloc_4997_, 3, v_auxDeclNGen_4984_);
lean_ctor_set(v_reuseFailAlloc_4997_, 4, v_traceState_4985_);
lean_ctor_set(v_reuseFailAlloc_4997_, 5, v___x_4993_);
lean_ctor_set(v_reuseFailAlloc_4997_, 6, v_messages_4986_);
lean_ctor_set(v_reuseFailAlloc_4997_, 7, v_infoState_4987_);
lean_ctor_set(v_reuseFailAlloc_4997_, 8, v_snapshotTasks_4988_);
v___x_4995_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
lean_object* v___x_4996_; 
v___x_4996_ = lean_st_ref_put(v___y_4975_, v___x_4995_);
v___y_4944_ = v___y_4972_;
v___y_4945_ = v___y_4973_;
v___y_4946_ = v___y_4974_;
v___y_4947_ = v___y_4977_;
v___y_4948_ = v___y_4978_;
v___y_4949_ = v___y_4976_;
v___y_4950_ = v___y_4975_;
goto v___jp_4943_;
}
}
}
else
{
v___y_4944_ = v___y_4972_;
v___y_4945_ = v___y_4973_;
v___y_4946_ = v___y_4974_;
v___y_4947_ = v___y_4977_;
v___y_4948_ = v___y_4978_;
v___y_4949_ = v___y_4976_;
v___y_4950_ = v___y_4975_;
goto v___jp_4943_;
}
}
v___jp_5000_:
{
lean_object* v___x_5006_; lean_object* v_env_5007_; uint8_t v___x_5008_; lean_object* v___x_5009_; uint8_t v___x_5010_; uint8_t v___x_5011_; 
v___x_5006_ = lean_st_ref_get(v___y_5005_);
v_env_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc_ref(v_env_5007_);
lean_dec(v___x_5006_);
v___x_5008_ = l_Lean_getPPInstantiateMVars(v_opts_5001_);
v___x_5009_ = l_Lean_diagnostics;
v___x_5010_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_delabCore_spec__1(v_opts_5001_, v___x_5009_);
v___x_5011_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5007_);
lean_dec_ref(v_env_5007_);
if (v___x_5010_ == 0)
{
if (v___x_5011_ == 0)
{
v___y_4944_ = v___x_5008_;
v___y_4945_ = v___y_5003_;
v___y_4946_ = v___y_5002_;
v___y_4947_ = v_opts_5001_;
v___y_4948_ = v___x_5010_;
v___y_4949_ = v___y_5004_;
v___y_4950_ = v___y_5005_;
goto v___jp_4943_;
}
else
{
v___y_4972_ = v___x_5008_;
v___y_4973_ = v___y_5003_;
v___y_4974_ = v___y_5002_;
v___y_4975_ = v___y_5005_;
v___y_4976_ = v___y_5004_;
v___y_4977_ = v_opts_5001_;
v___y_4978_ = v___x_5010_;
v___y_4979_ = v___x_5010_;
goto v___jp_4971_;
}
}
else
{
v___y_4972_ = v___x_5008_;
v___y_4973_ = v___y_5003_;
v___y_4974_ = v___y_5002_;
v___y_4975_ = v___y_5005_;
v___y_4976_ = v___y_5004_;
v___y_4977_ = v_opts_5001_;
v___y_4978_ = v___x_5010_;
v___y_4979_ = v___x_5011_;
goto v___jp_4971_;
}
}
v___jp_5012_:
{
if (v___y_5019_ == 0)
{
lean_dec_ref(v___y_5016_);
lean_del_object(v___x_4941_);
lean_inc_ref(v___y_5014_);
v_opts_5001_ = v___y_5014_;
v___y_5002_ = v___y_5015_;
v___y_5003_ = v___y_5017_;
v___y_5004_ = v___y_5013_;
v___y_5005_ = v___y_5018_;
goto v___jp_5000_;
}
else
{
lean_object* v___x_5021_; 
lean_dec(v_a_4939_);
lean_dec_ref(v_delab_4832_);
lean_dec(v_optionsPerPos_4831_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set_tag(v___x_4941_, 1);
lean_ctor_set(v___x_4941_, 0, v___y_5016_);
v___x_5021_ = v___x_4941_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___y_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
v___jp_5023_:
{
if (v___y_5030_ == 0)
{
lean_del_object(v___x_4941_);
lean_inc_ref(v___y_5025_);
v_opts_5001_ = v___y_5025_;
v___y_5002_ = v___y_5026_;
v___y_5003_ = v___y_5027_;
v___y_5004_ = v___y_5024_;
v___y_5005_ = v___y_5029_;
goto v___jp_5000_;
}
else
{
lean_object* v___x_5031_; 
lean_inc(v_a_4939_);
v___x_5031_ = l_Lean_Meta_isProof(v_a_4939_, v___y_5026_, v___y_5027_, v___y_5024_, v___y_5029_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; uint8_t v___x_5033_; 
lean_del_object(v___x_4941_);
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref_known(v___x_5031_, 1);
v___x_5033_ = lean_unbox(v_a_5032_);
if (v___x_5033_ == 0)
{
lean_dec(v_a_5032_);
lean_inc_ref(v___y_5025_);
v_opts_5001_ = v___y_5025_;
v___y_5002_ = v___y_5026_;
v___y_5003_ = v___y_5027_;
v___y_5004_ = v___y_5024_;
v___y_5005_ = v___y_5029_;
goto v___jp_5000_;
}
else
{
uint8_t v___x_5034_; lean_object* v___x_5035_; 
v___x_5034_ = lean_unbox(v_a_5032_);
lean_dec(v_a_5032_);
lean_inc_ref(v___y_5028_);
lean_inc_ref(v___y_5025_);
v___x_5035_ = l_Lean_Option_set___at___00Lean_PrettyPrinter_delabCore_spec__4(v___y_5025_, v___y_5028_, v___x_5034_);
v_opts_5001_ = v___x_5035_;
v___y_5002_ = v___y_5026_;
v___y_5003_ = v___y_5027_;
v___y_5004_ = v___y_5024_;
v___y_5005_ = v___y_5029_;
goto v___jp_5000_;
}
}
else
{
lean_object* v_a_5036_; uint8_t v___x_5037_; 
v_a_5036_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5031_, 1);
v___x_5037_ = l_Lean_Exception_isInterrupt(v_a_5036_);
if (v___x_5037_ == 0)
{
uint8_t v___x_5038_; 
lean_inc(v_a_5036_);
v___x_5038_ = l_Lean_Exception_isRuntime(v_a_5036_);
v___y_5013_ = v___y_5024_;
v___y_5014_ = v___y_5025_;
v___y_5015_ = v___y_5026_;
v___y_5016_ = v_a_5036_;
v___y_5017_ = v___y_5027_;
v___y_5018_ = v___y_5029_;
v___y_5019_ = v___x_5038_;
goto v___jp_5012_;
}
else
{
v___y_5013_ = v___y_5024_;
v___y_5014_ = v___y_5025_;
v___y_5015_ = v___y_5026_;
v___y_5016_ = v_a_5036_;
v___y_5017_ = v___y_5027_;
v___y_5018_ = v___y_5029_;
v___y_5019_ = v___x_5037_;
goto v___jp_5012_;
}
}
}
}
v___jp_5039_:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; 
v___x_5045_ = l_Lean_pp_proofs;
v___x_5046_ = l_Lean_Option_get_x3f___at___00Lean_PrettyPrinter_delabCore_spec__5(v_options_5043_, v___x_5045_);
v___x_5047_ = lean_box(0);
v___x_5048_ = l_Option_instBEq_beq___at___00Lean_PrettyPrinter_delabCore_spec__6(v___x_5046_, v___x_5047_);
lean_dec(v___x_5046_);
if (v___x_5048_ == 0)
{
v___y_5024_ = v___y_5042_;
v___y_5025_ = v_options_5043_;
v___y_5026_ = v___y_5040_;
v___y_5027_ = v___y_5041_;
v___y_5028_ = v___x_5045_;
v___y_5029_ = v___y_5044_;
v___y_5030_ = v___x_5048_;
goto v___jp_5023_;
}
else
{
uint8_t v___x_5049_; 
v___x_5049_ = l_Lean_Expr_isConst(v_a_4939_);
if (v___x_5049_ == 0)
{
v___y_5024_ = v___y_5042_;
v___y_5025_ = v_options_5043_;
v___y_5026_ = v___y_5040_;
v___y_5027_ = v___y_5041_;
v___y_5028_ = v___x_5045_;
v___y_5029_ = v___y_5044_;
v___y_5030_ = v___x_5048_;
goto v___jp_5023_;
}
else
{
lean_del_object(v___x_4941_);
lean_inc_ref(v_options_5043_);
v_opts_5001_ = v_options_5043_;
v___y_5002_ = v___y_5040_;
v___y_5003_ = v___y_5041_;
v___y_5004_ = v___y_5042_;
v___y_5005_ = v___y_5044_;
goto v___jp_5000_;
}
}
}
}
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5077_; 
lean_dec_ref(v_delab_4832_);
lean_dec(v_optionsPerPos_4831_);
v_a_5070_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5072_ = v___x_4938_;
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_4938_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
v___jp_4838_:
{
lean_object* v_infos_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v_infos_4841_ = lean_ctor_get(v_snd_4840_, 1);
lean_inc(v_infos_4841_);
lean_dec_ref(v_snd_4840_);
v___x_4842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4842_, 0, v_fst_4839_);
lean_ctor_set(v___x_4842_, 1, v_infos_4841_);
v___x_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
return v___x_4843_;
}
v___jp_4844_:
{
if (v___y_4851_ == 0)
{
if (lean_obj_tag(v___y_4847_) == 0)
{
lean_object* v___x_4852_; 
lean_dec_ref(v___y_4849_);
v___x_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4852_, 0, v___y_4847_);
return v___x_4852_;
}
else
{
lean_object* v_id_4853_; uint8_t v___x_4854_; 
v_id_4853_ = lean_ctor_get(v___y_4847_, 0);
v___x_4854_ = l_Lean_instBEqInternalExceptionId_beq(v___y_4848_, v_id_4853_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; 
lean_dec_ref(v___y_4849_);
v___x_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___y_4847_);
return v___x_4855_;
}
else
{
lean_object* v___x_4856_; lean_object* v___x_4857_; 
lean_dec_ref_known(v___y_4847_, 2);
v___x_4856_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__3, &l_Lean_PrettyPrinter_delabCore___redArg___closed__3_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__3);
v___x_4857_ = l_panic___at___00Lean_PrettyPrinter_delabCore_spec__0___redArg(v___x_4856_, v___y_4846_, v___y_4845_, v___y_4849_, v___y_4850_);
lean_dec_ref(v___y_4849_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v_fst_4859_; lean_object* v_snd_4860_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref_known(v___x_4857_, 1);
v_fst_4859_ = lean_ctor_get(v_a_4858_, 0);
lean_inc(v_fst_4859_);
v_snd_4860_ = lean_ctor_get(v_a_4858_, 1);
lean_inc(v_snd_4860_);
lean_dec(v_a_4858_);
v_fst_4839_ = v_fst_4859_;
v_snd_4840_ = v_snd_4860_;
goto v___jp_4838_;
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
v_a_4861_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4857_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4857_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
}
else
{
lean_object* v___x_4869_; 
lean_dec_ref(v___y_4849_);
v___x_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4869_, 0, v___y_4847_);
return v___x_4869_;
}
}
v___jp_4870_:
{
lean_object* v_toCold_4878_; lean_object* v_currRecDepth_4879_; uint8_t v_diag_4880_; uint8_t v_suppressElabErrors_4881_; lean_object* v_currNamespace_4882_; lean_object* v_openDecls_4883_; lean_object* v_lctx_4884_; uint8_t v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v_toCold_4878_ = lean_ctor_get(v___y_4876_, 0);
v_currRecDepth_4879_ = lean_ctor_get(v___y_4876_, 1);
v_diag_4880_ = lean_ctor_get_uint8(v___y_4876_, sizeof(void*)*3);
v_suppressElabErrors_4881_ = lean_ctor_get_uint8(v___y_4876_, sizeof(void*)*3 + 1);
v_currNamespace_4882_ = lean_ctor_get(v_toCold_4878_, 4);
v_openDecls_4883_ = lean_ctor_get(v_toCold_4878_, 5);
v_lctx_4884_ = lean_ctor_get(v___y_4874_, 2);
v___x_4885_ = l_Lean_Options_getInPattern(v___y_4872_);
lean_dec_ref(v___y_4872_);
v___x_4886_ = l_Lean_SubExpr_mkRoot(v___y_4871_);
v___x_4887_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_lctx_4884_);
v___x_4888_ = lean_local_ctx_num_indices(v_lctx_4884_);
lean_inc(v_openDecls_4883_);
lean_inc(v_currNamespace_4882_);
v___x_4889_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4889_, 0, v_optionsPerPos_4873_);
lean_ctor_set(v___x_4889_, 1, v_currNamespace_4882_);
lean_ctor_set(v___x_4889_, 2, v_openDecls_4883_);
lean_ctor_set(v___x_4889_, 3, v___x_4886_);
lean_ctor_set(v___x_4889_, 4, v___x_4887_);
lean_ctor_set(v___x_4889_, 5, v___x_4888_);
lean_ctor_set_uint8(v___x_4889_, sizeof(void*)*6, v___x_4885_);
v___x_4890_ = lean_obj_once(&l_Lean_PrettyPrinter_delabCore___redArg___closed__5, &l_Lean_PrettyPrinter_delabCore___redArg___closed__5_once, _init_l_Lean_PrettyPrinter_delabCore___redArg___closed__5);
v___x_4891_ = lean_st_mk_ref(v___x_4890_);
v___x_4892_ = lean_box(0);
lean_inc(v_currRecDepth_4879_);
lean_inc_ref(v_toCold_4878_);
v___x_4893_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4893_, 0, v_toCold_4878_);
lean_ctor_set(v___x_4893_, 1, v_currRecDepth_4879_);
lean_ctor_set(v___x_4893_, 2, v___x_4892_);
lean_ctor_set_uint8(v___x_4893_, sizeof(void*)*3, v_diag_4880_);
lean_ctor_set_uint8(v___x_4893_, sizeof(void*)*3 + 1, v_suppressElabErrors_4881_);
lean_inc(v___y_4877_);
lean_inc(v___y_4875_);
lean_inc_ref(v___y_4874_);
lean_inc(v___x_4891_);
v___x_4894_ = lean_apply_7(v_delab_4832_, v___x_4889_, v___x_4891_, v___y_4874_, v___y_4875_, v___x_4893_, v___y_4877_, lean_box(0));
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v_a_4895_; lean_object* v___x_4896_; 
lean_dec_ref(v___y_4876_);
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
lean_inc(v_a_4895_);
lean_dec_ref_known(v___x_4894_, 1);
v___x_4896_ = lean_st_ref_get(v___x_4891_);
lean_dec(v___x_4891_);
v_fst_4839_ = v_a_4895_;
v_snd_4840_ = v___x_4896_;
goto v___jp_4838_;
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; 
lean_dec(v___x_4891_);
v_a_4897_ = lean_ctor_get(v___x_4894_, 0);
lean_inc(v_a_4897_);
lean_dec_ref_known(v___x_4894_, 1);
v___x_4898_ = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
v___x_4899_ = l_Lean_Exception_isInterrupt(v_a_4897_);
if (v___x_4899_ == 0)
{
uint8_t v___x_4900_; 
lean_inc(v_a_4897_);
v___x_4900_ = l_Lean_Exception_isRuntime(v_a_4897_);
v___y_4845_ = v___y_4875_;
v___y_4846_ = v___y_4874_;
v___y_4847_ = v_a_4897_;
v___y_4848_ = v___x_4898_;
v___y_4849_ = v___y_4876_;
v___y_4850_ = v___y_4877_;
v___y_4851_ = v___x_4900_;
goto v___jp_4844_;
}
else
{
v___y_4845_ = v___y_4875_;
v___y_4846_ = v___y_4874_;
v___y_4847_ = v_a_4897_;
v___y_4848_ = v___x_4898_;
v___y_4849_ = v___y_4876_;
v___y_4850_ = v___y_4877_;
v___y_4851_ = v___x_4899_;
goto v___jp_4844_;
}
}
}
v___jp_4901_:
{
uint8_t v___x_4908_; 
v___x_4908_ = l_Lean_getPPAll(v___y_4902_);
if (v___x_4908_ == 0)
{
uint8_t v___x_4909_; 
v___x_4909_ = l_Lean_getPPAnalyze(v___y_4902_);
if (v___x_4909_ == 0)
{
v___y_4871_ = v_e_4903_;
v___y_4872_ = v___y_4902_;
v_optionsPerPos_4873_ = v_optionsPerPos_4831_;
v___y_4874_ = v___y_4904_;
v___y_4875_ = v___y_4905_;
v___y_4876_ = v___y_4906_;
v___y_4877_ = v___y_4907_;
goto v___jp_4870_;
}
else
{
if (lean_obj_tag(v_optionsPerPos_4831_) == 0)
{
v___y_4871_ = v_e_4903_;
v___y_4872_ = v___y_4902_;
v_optionsPerPos_4873_ = v_optionsPerPos_4831_;
v___y_4874_ = v___y_4904_;
v___y_4875_ = v___y_4905_;
v___y_4876_ = v___y_4906_;
v___y_4877_ = v___y_4907_;
goto v___jp_4870_;
}
else
{
lean_object* v___x_4910_; 
lean_inc_ref(v_e_4903_);
v___x_4910_ = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(v_e_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v___y_4871_ = v_e_4903_;
v___y_4872_ = v___y_4902_;
v_optionsPerPos_4873_ = v_a_4911_;
v___y_4874_ = v___y_4904_;
v___y_4875_ = v___y_4905_;
v___y_4876_ = v___y_4906_;
v___y_4877_ = v___y_4907_;
goto v___jp_4870_;
}
else
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
lean_dec_ref(v___y_4906_);
lean_dec_ref(v_e_4903_);
lean_dec_ref(v___y_4902_);
lean_dec_ref(v_delab_4832_);
v_a_4912_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4910_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4910_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
}
}
else
{
v___y_4871_ = v_e_4903_;
v___y_4872_ = v___y_4902_;
v_optionsPerPos_4873_ = v_optionsPerPos_4831_;
v___y_4874_ = v___y_4904_;
v___y_4875_ = v___y_4905_;
v___y_4876_ = v___y_4906_;
v___y_4877_ = v___y_4907_;
goto v___jp_4870_;
}
}
v___jp_4920_:
{
uint8_t v___x_4927_; 
v___x_4927_ = l_Lean_getPPBeta(v___y_4921_);
if (v___x_4927_ == 0)
{
v___y_4902_ = v___y_4921_;
v_e_4903_ = v_e_4922_;
v___y_4904_ = v___y_4923_;
v___y_4905_ = v___y_4924_;
v___y_4906_ = v___y_4925_;
v___y_4907_ = v___y_4926_;
goto v___jp_4901_;
}
else
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Core_betaReduce(v_e_4922_, v___y_4925_, v___y_4926_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
v___y_4902_ = v___y_4921_;
v_e_4903_ = v_a_4929_;
v___y_4904_ = v___y_4923_;
v___y_4905_ = v___y_4924_;
v___y_4906_ = v___y_4925_;
v___y_4907_ = v___y_4926_;
goto v___jp_4901_;
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
lean_dec_ref(v___y_4925_);
lean_dec_ref(v___y_4921_);
lean_dec_ref(v_delab_4832_);
lean_dec(v_optionsPerPos_4831_);
v_a_4930_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4928_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4928_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___redArg___boxed(lean_object* v_e_5078_, lean_object* v_optionsPerPos_5079_, lean_object* v_delab_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5078_, v_optionsPerPos_5079_, v_delab_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
lean_dec(v_a_5082_);
lean_dec_ref(v_a_5081_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* v_00_u03b1_5087_, lean_object* v_e_5088_, lean_object* v_optionsPerPos_5089_, lean_object* v_delab_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v___x_5096_; 
v___x_5096_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5088_, v_optionsPerPos_5089_, v_delab_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___boxed(lean_object* v_00_u03b1_5097_, lean_object* v_e_5098_, lean_object* v_optionsPerPos_5099_, lean_object* v_delab_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Lean_PrettyPrinter_delabCore(v_00_u03b1_5097_, v_e_5098_, v_optionsPerPos_5099_, v_delab_5100_, v_a_5101_, v_a_5102_, v_a_5103_, v_a_5104_);
lean_dec(v_a_5104_);
lean_dec_ref(v_a_5103_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* v_e_5108_, lean_object* v_optionsPerPos_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = ((lean_object*)(l_Lean_PrettyPrinter_delab___closed__0));
v___x_5116_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_5108_, v_optionsPerPos_5109_, v___x_5115_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5125_; 
v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5119_ = v___x_5116_;
v_isShared_5120_ = v_isSharedCheck_5125_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5116_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5125_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v_fst_5121_; lean_object* v___x_5123_; 
v_fst_5121_ = lean_ctor_get(v_a_5117_, 0);
lean_inc(v_fst_5121_);
lean_dec(v_a_5117_);
if (v_isShared_5120_ == 0)
{
lean_ctor_set(v___x_5119_, 0, v_fst_5121_);
v___x_5123_ = v___x_5119_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_fst_5121_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
v_a_5126_ = lean_ctor_get(v___x_5116_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5128_ = v___x_5116_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5116_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab___boxed(lean_object* v_e_5134_, lean_object* v_optionsPerPos_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l_Lean_PrettyPrinter_delab(v_e_5134_, v_optionsPerPos_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
lean_dec(v_a_5139_);
lean_dec_ref(v_a_5138_);
lean_dec(v_a_5137_);
lean_dec_ref(v_a_5136_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5206_; uint8_t v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5206_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5207_ = 0;
v___x_5208_ = ((lean_object*)(l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn___closed__24_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_));
v___x_5209_ = l_Lean_registerTraceClass(v___x_5206_, v___x_5207_, v___x_5208_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v___x_5210_; lean_object* v___x_5211_; 
lean_dec_ref_known(v___x_5209_, 1);
v___x_5210_ = ((lean_object*)(l_Lean_PrettyPrinter_delabCore___redArg___closed__7));
v___x_5211_ = l_Lean_registerTraceClass(v___x_5210_, v___x_5207_, v___x_5208_);
return v___x_5211_;
}
else
{
return v___x_5209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2____boxed(lean_object* v_a_5212_){
_start:
{
lean_object* v_res_5213_; 
v_res_5213_ = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
return v_res_5213_;
}
}
lean_object* runtime_initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_2007592451____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabFailureId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabFailureId);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_3103770728____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabAttribute);
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_delabAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_delabAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_688057830____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute);
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute___regBuiltin_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_Delaborator_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Delaborator_Basic_407216755____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_KeyedDeclsAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
